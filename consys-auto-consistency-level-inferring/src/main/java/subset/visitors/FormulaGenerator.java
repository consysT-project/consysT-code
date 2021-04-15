package subset.visitors;

import com.microsoft.z3.*;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.*;
import subset.Z3Checker;
import subset.z3_model.InternalArray;
import subset.z3_model.InternalScope;
import subset.z3_model.InternalVar;

import java.util.*;
import java.util.stream.Collectors;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
public class FormulaGenerator {
  Context context = Z3Checker.context;
  /**
   * The counter is increased every time a quantifier has been instantiated so that the SMT solver
   * does not mix up the quantifiers
   */
  private int quantifierCounter = 0;

  /**
   * This method calls the correct visitXYZ(...) method for a given JML expression
   *
   * @param expression the expression to be visited
   * @return the corresponding Z3 expression
   */
  public Expr visitExpression(Expression expression, InternalScope scope) {
    // "\result" is the result reference
    if (expression instanceof JmlResultReference) return scope.getCurrentReturnVariable();

    // literals can be translated directly
    if (expression instanceof IntLiteral) return context.mkInt(((IntLiteral) expression).value);
    if (expression instanceof DoubleLiteral) {
      double value = ((DoubleLiteral) expression).constant.doubleValue();
      return context.mkFPToReal(context.mkFP(value, context.mkFPSortDouble()));
    }
    if (expression instanceof TrueLiteral) return context.mkTrue();
    if (expression instanceof FalseLiteral) return context.mkFalse();

    // expressions like addition, modulo, and, or, ...
    if (expression instanceof BinaryExpression) {
      return visitBinaryExpression((BinaryExpression) expression, scope);
    }

    // one reference of a variable: "a"
    if (expression instanceof JmlSingleNameReference) {
      return visitJmlSingleReference((JmlSingleNameReference) expression, scope);
    }

    // "\old(...)"
    if (expression instanceof JmlOldExpression) {
      return visitOldExpression((JmlOldExpression) expression, scope);
    }

    // "some.other"
    if (expression instanceof JmlQualifiedNameReference) {
      return visitJmlQualifiedNameReference((JmlQualifiedNameReference) expression, scope);
    }

    // "array[index]"
    if (expression instanceof JmlArrayReference) {
      return visitJmlArrayReference((JmlArrayReference) expression, scope);
    }

    // "({\forall | \exists | \sum} boundVarDeclarations; rangeExpression; body)"
    if (expression instanceof JmlQuantifiedExpression) {
      return visitJmlQuantifiedExpression((JmlQuantifiedExpression) expression, scope);
    }

    // "method()", "other.method()"
    if (expression instanceof JmlMessageSend) {
      return visitJmlMessageSend((JmlMessageSend) expression, scope);
    }
    return null;
  }

  /**
   * Visit every kind of binary expression. Note, that bitwise operators are translated like their
   * logical pendant.
   *
   * @return e Z3 expression that uses the correct operator
   */
  public Expr visitBinaryExpression(BinaryExpression binaryExpression, InternalScope scope) {
    // translate expressions from both operands
    Expr left = visitExpression(binaryExpression.left, scope);
    Expr right = visitExpression(binaryExpression.right, scope);

    // get operator value and construct corresponding Z3 expression
    String s = binaryExpression.operatorToString();
    if ((s.equals("&&") || s.equals("&"))
        && left instanceof BoolExpr
        && right instanceof BoolExpr) {
      return context.mkAnd((BoolExpr) left, (BoolExpr) right);
    }

    if ((s.equals("||") || s.equals("|"))
        && left instanceof BoolExpr
        && right instanceof BoolExpr) {
      return context.mkOr((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("<") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkLt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("<=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkLe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkGt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkGe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("^") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return context.mkXor((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("/") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkDiv((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("-") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkSub((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("+") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkAdd((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("*") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return context.mkMul((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("%") && left instanceof IntExpr && right instanceof IntExpr) {
      return context.mkMod((IntExpr) left, (IntExpr) right);
    }

    /* if values need to be set, this point is used as not all equality operators are only used
    for equality constraints
    */
    if (left != null && right != null && (s.equals("<==>") || s.equals("=") || s.equals("=="))) {
      // set result expression for current scope
      if (binaryExpression.left instanceof JmlResultReference) {
        scope.setCurrentReturnExpression(right);
      }

      // set array size
      else if (left instanceof SeqExpr && right instanceof IntExpr) {
        InternalVar arr = scope.getClassVariable(left.getString());
        if (arr instanceof InternalArray) {
          ((InternalArray) arr)
              .setSize(new IntegerValueVisitor().visitExpression(binaryExpression.right, scope));
          return context.mkTrue();
        }
      }
      return context.mkEq(left, right);
    }

    if (s.equals("==>") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return context.mkImplies((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("<==") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return context.mkImplies((BoolExpr) right, (BoolExpr) left);
    }

    if (left != null && right != null && (s.equals("<=!=>") || s.equals("!=")))
      return context.mkNot(context.mkEq(left, right));
    return null;
  }

  /**
   * Visits the reference of a single variable name. The name is resolved using the {@link
   * InternalScope}, and the constant describing the poststate is used. In order to reference the
   * prestate, the reference can be encapsuled in an {@code \old} expression.
   *
   * @return the Z3 variable used for the new state or {@code null} if no variable with the
   *     referenced name could be found
   */
  public Expr visitJmlSingleReference(
      JmlSingleNameReference jmlSingleNameReference, InternalScope scope) {
    String variableName = String.valueOf(jmlSingleNameReference.token);
    // get either new value from class variables or expression from scope
    if (scope.getClassVariables().containsKey(variableName))
      return scope.getClassVariable(variableName).getNewValue();
    else if (scope.getLocalVariables().containsKey(variableName))
      return scope.getLocalVariable(variableName);
    return null;
  }

  /**
   * Visits {@code \old(...)} expressions and substitutes every occurring variable with its prestate
   * Z3 constant.
   *
   * @return expression where every occurrence of a state variable is substituted with the variable
   *     depicting the old state
   */
  public Expr visitOldExpression(JmlOldExpression jmlOldExpression, InternalScope scope) {
    // translate the whole expression inside \old(...)
    Expr subExpr = visitExpression(jmlOldExpression.expression, scope);

    /*
    Gather both prestate and poststate constants
     */
    int varSize = scope.getClassVariables().size();
    Expr[] newVars = new Expr[varSize];
    Expr[] oldVars = new Expr[varSize];

    newVars =
        scope.getClassVariables().values().stream()
            .map(InternalVar::getNewValue)
            .collect(Collectors.toList())
            .toArray(newVars);

    oldVars =
        scope.getClassVariables().values().stream()
            .map(InternalVar::getOldValue)
            .collect(Collectors.toList())
            .toArray(oldVars);

    // substitute all occurrences of poststate variables with the prestate ones
    return subExpr.substitute(newVars, oldVars);
  }

  /**
   * Visits expressions like {@code something.other} Assumes that the qualified name reference
   * refers to expressions of the form class.variable, concatenation is currently not supported.
   *
   * @return result of evaluating className.varName
   */
  public Expr visitJmlQualifiedNameReference(
      JmlQualifiedNameReference jmlQualifiedNameReference, InternalScope scope) {
    // in this case, it is class.variableName
    if (jmlQualifiedNameReference.tokens.length == 2) {
      String className = String.valueOf(jmlQualifiedNameReference.tokens[0]);
      String varName = String.valueOf(jmlQualifiedNameReference.tokens[1]);

      // the "other" variable needs to be used to depict the state relation of a merge constraint
      if (className.equals("other") && scope.insideMergeFunction) {
        return scope.getClassVariable(varName).getOtherValue();
      }

      // Get variable from scope -> in this case return new value or argument value
      else if (className.equals("this")) {
        // variable is some class variable
        if (scope.getClassVariables().containsKey(varName)) {
          return scope.getClassVariable(varName).getNewValue();
        }
        // variable is local variable
        else if (scope.getLocalVariables().containsKey(varName)) {
          return scope.getLocalVariable(varName);
        }
      }

      // array.length expected in constructor
      else if (scope.hasClassVariable(className) && varName.equals("length")) {
        return context.mkString(className);
      }
    }
    return null;
  }

  /**
   * Visits select expressions like {@code array[index]}
   *
   * @return a Z3 select expressions or {@code null} if the translation did not succeed
   */
  public Expr visitJmlArrayReference(JmlArrayReference jmlArrayReference, InternalScope scope) {
    Expr array = visitExpression(jmlArrayReference.receiver, scope);

    if (array instanceof ArrayExpr) {
      // get index expression
      Expr index = visitExpression(jmlArrayReference.position, scope);
      return context.mkSelect((ArrayExpr) array, index);
    }

    return null;
  }

  /**
   * Visits quantified expressions and translates universal/existential quantification directly to
   * Z3 quantifiers. Sum quantification is only supported if it is applied on an array reference
   * without range constraints.
   *
   * @return
   */
  public Expr visitJmlQuantifiedExpression(
      JmlQuantifiedExpression jmlQuantifiedExpression, InternalScope scope) {
    // boundVariables declaration: introduce new local scope
    Map<String, Expr> newLocalVars = new HashMap<>(scope.getLocalVariables());
    Expr[] boundConstants = new Expr[jmlQuantifiedExpression.boundVariables.length];
    int i = 0;
    for (LocalDeclaration localDeclaration : jmlQuantifiedExpression.boundVariables) {
      Expr localVar = visitLocalDeclaration(localDeclaration, scope);
      newLocalVars.put(String.valueOf(localDeclaration.name), localVar);
      boundConstants[i] = localVar;
      i++;
    }

    // new scope for inside the quantifier
    InternalScope newLocalScope =
        new InternalScope(
            scope.getClassVariables(),
            newLocalVars,
            scope.getReturnValues(),
            scope.getCurrentReturnVariable(),
            scope.insideMergeFunction);

    // get range and body expression
    Expr rangeExpr = visitExpression(jmlQuantifiedExpression.range, newLocalScope);
    Expr bodyExpr = visitExpression(jmlQuantifiedExpression.body, newLocalScope);

    // this applies to \forall and \exists expressions
    if (rangeExpr instanceof BoolExpr && bodyExpr instanceof BoolExpr) {
      // range ==> body
      BoolExpr finalBodyExpr = context.mkImplies((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);

      // quantifier: forall or exists
      Expr quantifiedExpr =
          context.mkQuantifier(
              jmlQuantifiedExpression.quantifier.lexeme.equalsIgnoreCase("\\forall"),
              boundConstants,
              finalBodyExpr,
              1,
              null,
              null,
              context.mkSymbol("Q_" + quantifierCounter),
              context.mkSymbol("Sk_" + quantifierCounter));

      // increment for future quantifiers
      quantifierCounter++;

      return quantifiedExpr;
    }

    // this applies to \sum expressions
    if (rangeExpr instanceof BoolExpr
        && bodyExpr instanceof ArithExpr
        && jmlQuantifiedExpression.quantifier.lexeme.equalsIgnoreCase("\\sum")) {
      // \sum int b; b>=0 && b<10; \old(incs[b])
      // only support whole array expressions as of now
      // get array and internalArray instance and call combine with ADD
      if (bodyExpr.isSelect()) {
        ArrayExpr selectedArray = (ArrayExpr) bodyExpr.getArgs()[0];
        // name is something like old_array, new_array or other_array
        String name =
            selectedArray.toString().substring(selectedArray.toString().lastIndexOf("_") + 1);
        if (scope.getClassVariable(name) instanceof InternalArray) {
          InternalArray arr = (InternalArray) scope.getClassVariable(name);
          return arr.combineValues(
              InternalArray.Combiner.ADDITION,
              selectedArray,
              ((ArraySort) arr.getSort()).getRange().getSortKind());
        }
      }
    }

    return null;
  }

  /**
   * Visits method call like {@code getValue()} or {@code other.getValue()}.
   *
   * @return the result expression of the called method if it has one, {@code null} otherwise
   */
  public Expr visitJmlMessageSend(JmlMessageSend jmlMessageSend, InternalScope scope) {
    Expr methodReturnValue = scope.getReturnValue(String.valueOf(jmlMessageSend.selector));

    if (methodReturnValue != null) {
      // now distinguish between this and other -> check if its a this reference
      if (jmlMessageSend.receiver instanceof ThisReference) {
        return methodReturnValue;
      } else {
        // only method calls within the same class supported
        int varSize = scope.getClassVariables().size();
        Expr[] newVars = new Expr[varSize];
        Expr[] otherVars = new Expr[varSize];
        newVars =
            scope.getClassVariables().values().stream()
                .map(InternalVar::getNewValue)
                .collect(Collectors.toList())
                .toArray(newVars);
        otherVars =
            scope.getClassVariables().values().stream()
                .map(InternalVar::getOtherValue)
                .collect(Collectors.toList())
                .toArray(otherVars);
        return methodReturnValue.substitute(newVars, otherVars);
      }
    }

    return null;
  }

  /*
   ***************************************************************************************************************
   **************************************** Statements, called separately ****************************************
   ***************************************************************************************************************
   */

  /**
   * This visit method is called inside quantifier expressions in order to handle bound variables
   *
   * @return Z3 variable representing the bound variable
   */
  public Expr visitLocalDeclaration(LocalDeclaration localDeclaration, InternalScope scope) {
    // type
    Sort type = new TypeGenerator().visitTypeReference(localDeclaration.type);

    // return new constant
    if (type != null) {
      return context.mkConst(String.valueOf(localDeclaration.name) + quantifierCounter, type);
    }

    return null;
  }

  /**
   * This visit method translates an assignable clause into a postcondition. {@code assignable
   * \nothing} translates to setting all prestate constants equal to the poststate constants. {@code
   * assignable a} does the same but leaves {@code a} out, also {@code assignable a[3]} but for
   * a[3].
   *
   * @return the created postcondition from the assignable clause
   */
  public BoolExpr visitJmlAssignableClause(
      JmlAssignableClause jmlAssignableClause, InternalScope scope) {
    /*
     *************************** assignable \nothing ***************************
     */
    if (jmlAssignableClause.expr instanceof JmlKeywordExpression) {
      if (jmlAssignableClause.expr.equals(JmlKeywordExpression.NOTHING)) {

        // get all prestate and poststate variables
        BoolExpr res = context.mkTrue();
        Expr[] newVars = new Expr[scope.getClassVariables().size()];
        Expr[] oldVars = new Expr[scope.getClassVariables().size()];

        newVars =
            scope.getClassVariables().values().stream()
                .map(InternalVar::getNewValue)
                .collect(Collectors.toList())
                .toArray(newVars);
        oldVars =
            scope.getClassVariables().values().stream()
                .map(InternalVar::getOldValue)
                .collect(Collectors.toList())
                .toArray(oldVars);

        // set all prestate vars == poststate vars
        for (int i = 0; i < scope.getClassVariables().size(); i++) {
          res = context.mkAnd(res, context.mkEq(newVars[i], oldVars[i]));
        }
        return res;
      }
    }

    /*
     ************************** assignable (a | a[n]) **************************
     */
    else if (jmlAssignableClause.expr instanceof JmlStoreRefListExpression) {
      // collect all java variable references from the assignable clause
      Expression[] references = ((JmlStoreRefListExpression) jmlAssignableClause.expr).exprList;
      BoolExpr resultingPostCondition = context.mkTrue();

      // collect all names of the variables that are mentioned
      List<String> mentionedVariables = new ArrayList<>();
      for (Expression ref : references) {
        // a, b, c -> JmlSingleNameReference
        if (ref instanceof JmlSingleNameReference) {
          mentionedVariables.add(String.valueOf(((JmlSingleNameReference) ref).token));
        }

        // c[3] -> JmlArrayReference
        // jml array reference: receiver is single name ref, position is number
        else if (ref instanceof JmlArrayReference
            && ((JmlArrayReference) ref).receiver instanceof JmlSingleNameReference) {
          String arrayName =
              String.valueOf(((JmlSingleNameReference) ((JmlArrayReference) ref).receiver).token);
          mentionedVariables.add(arrayName);

          // get array from scope
          InternalArray array = (InternalArray) scope.getClassVariable(arrayName);

          // get position
          int changedIndex =
              new IntegerValueVisitor().visitExpression(((JmlArrayReference) ref).position, scope);

          // add resulting postcondition
          resultingPostCondition =
              context.mkAnd(
                  resultingPostCondition,
                  InternalArray.oneFieldChanged(
                      array.getOldValue(), array.getNewValue(), changedIndex, array.getSize()));
        }
      }

      /*
       * for the rest of the variables, prestate == poststate remains
       */

      List<InternalVar> notMentioned =
          scope.getClassVariables().entrySet().stream()
              .filter(x -> !mentionedVariables.contains(x.getKey()))
              .map(Map.Entry::getValue)
              .collect(Collectors.toList());

      for (InternalVar notChanging : notMentioned) {
        if (notChanging instanceof InternalArray) {
          resultingPostCondition =
              context.mkAnd(
                  resultingPostCondition,
                  InternalArray.sameFields(
                      ((InternalArray) notChanging).getOldValue(),
                      ((InternalArray) notChanging).getNewValue(),
                      ((InternalArray) notChanging).getSize()));
        } else {
          resultingPostCondition =
              context.mkAnd(
                  resultingPostCondition,
                  context.mkEq(notChanging.getOldValue(), notChanging.getNewValue()));
        }
      }

      return resultingPostCondition;
    }

    return null;
  }
}
