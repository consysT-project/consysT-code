package de.tuda.stg.consys.invariants.subset.visitors;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.Z3Checker;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalArray;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalScope;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalVar;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.*;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
@SuppressWarnings("rawtypes")
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

    if (expression == null)
      throw new NullPointerException("expression was null");


    // literal expression: 10, -5.6, true, ...
    if (expression instanceof Literal) {
      return visitLiteralExpression((Literal) expression, scope);
    }


    // one reference of a variable: "a"
    if (expression instanceof JmlSingleNameReference) {
      return visitJmlSingleReference((JmlSingleNameReference) expression, scope);
    }

    // \result is the result reference
    if (expression instanceof JmlResultReference) return scope.getCurrentReturnVariable();

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

    // expressions with operators: a + b, a ? b : c, !a ...
    if (expression instanceof OperatorExpression) {
      return visitOperatorExpression((OperatorExpression) expression, scope);
    }

    throw new UnsupportedJMLExpression(expression);
  }

  public Expr visitLiteralExpression(org.eclipse.jdt.internal.compiler.ast.Literal literalExpression, InternalScope scope) {
    // literals can be translated directly
    if (literalExpression instanceof IntLiteral)
      return context.mkInt(((IntLiteral) literalExpression).value);

    if (literalExpression instanceof DoubleLiteral) {
      double value = ((DoubleLiteral) literalExpression).constant.doubleValue();
      return context.mkFPToReal(context.mkFP(value, context.mkFPSortDouble()));
    }

    if (literalExpression instanceof TrueLiteral)
      return context.mkTrue();

    if (literalExpression instanceof FalseLiteral)
      return context.mkFalse();

    throw new UnsupportedJMLExpression(literalExpression);
  }

  public Expr visitOperatorExpression(OperatorExpression operatorExpression, InternalScope scope) {
    // !a ...
    if (operatorExpression instanceof UnaryExpression) {
      return visitUnaryExpression((UnaryExpression) operatorExpression, scope);
    }

    // expressions like addition, modulo, and, or, ...
    if (operatorExpression instanceof BinaryExpression) {
      return visitBinaryExpression((BinaryExpression) operatorExpression, scope);
    }

    if (operatorExpression instanceof ConditionalExpression) {
      return visitConditionalExpression((ConditionalExpression) operatorExpression, scope);
    }

    throw new UnsupportedJMLExpression(operatorExpression);
  }

  public Expr visitUnaryExpression(UnaryExpression unaryExpression, InternalScope scope) {
    Expr expr = visitExpression(unaryExpression.expression, scope);

    throw new UnsupportedJMLExpression(unaryExpression);
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



    if (s.equals("&&") || s.equals("&")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return context.mkAnd((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArgumentsExpression(binaryExpression);
    }

    if (s.equals("||") || s.equals("|")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return context.mkOr((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArgumentsExpression(binaryExpression);
    }

    //TODO: Add WrongJMLArgumentsExpression to all cases
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

    throw new UnsupportedJMLExpression(binaryExpression);
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

    throw new WrongJMLArgumentsExpression(jmlSingleNameReference);
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

  public Expr visitConditionalExpression(ConditionalExpression conditionalExpression, InternalScope scope) {
    Expr cond = visitExpression(conditionalExpression.condition, scope);
    Expr thenBranch = visitExpression(conditionalExpression.valueIfTrue, scope);
    Expr elseBranch = visitExpression(conditionalExpression.valueIfFalse, scope);

    if (cond instanceof BoolExpr) {
      BoolExpr condBool = (BoolExpr) cond;

      return context.mkITE(condBool, thenBranch, elseBranch);
    }

    throw new WrongJMLArgumentsExpression(conditionalExpression);

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

    throw new WrongJMLArgumentsExpression(jmlQualifiedNameReference);
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

    throw new WrongJMLArgumentsExpression(jmlArrayReference);
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

    //quantifier operator as string
    String quantifier = jmlQuantifiedExpression.quantifier.lexeme;

    // this applies to \forall and \exists expressions
    if (quantifier.equals(JmlQuantifier.EXISTS) || quantifier.equals(JmlQuantifier.FORALL)) {

      if (rangeExpr instanceof  BoolExpr && bodyExpr instanceof BoolExpr) {
        // range ==> body
        BoolExpr finalBodyExpr = context.mkImplies((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);

        boolean isForall = quantifier.equals(JmlQuantifier.FORALL);

        // quantifier: forall or exists
        Expr quantifiedExpr =
                context.mkQuantifier(
                        isForall, //decide whether to create forall or exists quantifier
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

      throw new WrongJMLArgumentsExpression(jmlQuantifiedExpression);
    }

    // this applies to \sum expressions
    if (quantifier.equals(JmlQuantifier.SUM)) {
      if (rangeExpr instanceof BoolExpr && bodyExpr instanceof ArithExpr) {

        // whole array expressions as of now
        // \sum int b; b>=0 && b<10; \old(incs[b])
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
        } else {
          //The general case for summation
          // NOTE: Summation always (!) start at i = 0, and increase i in every step by 1.
          System.err.println("Warning! \\sum only supports sums starting at 0.");

//          ctx = Context()
//          symSum = RecFunction('symSum', IntSort(ctx), IntSort(ctx), IntSort(ctx))
//          a = Int('a',ctx)
//          b = Int('b',ctx)
//          RecAddDefinition(symSum, [a,b], If(a > b, 0, a + symSum(a+1,b)))
//          x = Int('x',ctx)
//
//          s = Solver(ctx=ctx)
//          s.add(symSum(1,5) == x)
//          print(s.check())
//          print(s.model())

          if (jmlQuantifiedExpression.boundVariables.length != 1) {
            throw new WrongJMLArgumentsExpression(jmlQuantifiedExpression);
          }


          FuncDecl sumFunc = context.mkRecFuncDecl(
                  context.mkSymbol("$SUM_" + quantifierCounter),
                  new Sort[] { context.getIntSort() },
                  bodyExpr.getSort()
          );


          // increment for future quantifiers
          quantifierCounter++;

          Expr indexVar = boundConstants[0];

          /* Build body. Example:
            \sum int i; i >= 0 && i <= size; arr[i] * 2
            -->
            sumFunc(int i) { if (i >= 0 && i <= size) then (arr[i] * 2) + sumFunc(i + 1) else 0 }
           */
          Expr sumBody =
                  context.mkITE(rangeExpr, // if (i in range)
                          // then
                          context.mkAdd(
                                  // body + sumFunc(i + 1)
                                  bodyExpr,
                                  context.mkApp(sumFunc, context.mkAdd(indexVar, context.mkInt(1)))
                          ),
                          // else
                          context.mkInt(0)
                          );

          // Create the func def
          context.AddRecDef(sumFunc, boundConstants, sumBody);

          // Apply sumFunc to 0 and return as expression
          Expr result = context.mkApp(sumFunc, context.mkInt(0));

          return result;
        }


      }

      throw new WrongJMLArgumentsExpression(jmlQuantifiedExpression);
    }

    throw new UnsupportedJMLExpression(jmlQuantifiedExpression);
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

    throw new WrongJMLArgumentsExpression(jmlMessageSend);
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

    throw new IllegalArgumentException(localDeclaration.toString());
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

    throw new IllegalArgumentException(jmlAssignableClause.toString());
  }
}
