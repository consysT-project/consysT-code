package de.tuda.stg.consys.invariants.subset.parser;

import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.Z3Utils;
import de.tuda.stg.consys.invariants.subset.visitors.IntegerValueVisitor;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalArray;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalScope;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalVar;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.*;

import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
@SuppressWarnings("rawtypes")
public class BaseExpressionParser extends ExpressionParser {

  // The z3 context used for creating expressions
  protected final Context ctx;
  // Local variables from jml quantifiers.
  private final Map<String, Expr> localVariables = Maps.newHashMap();

  private int nextFreshId = 0;

  private int getFreshId() {
    return nextFreshId++;
  }


  public BaseExpressionParser(Context ctx) {
    this.ctx = ctx;
  }

  /**
   * This method calls the correct visitXYZ(...) method for a given JML expression
   *
   * @param expression the expression to be visited
   * @return the corresponding Z3 expression
   */
  @Override
  public Expr parseExpression(Expression expression) {

    if (expression == null)
      throw new NullPointerException("expression was null");

    // literal expression: 10, -5.6, true, ...
    if (expression instanceof Literal) {
      return parseLiteral((Literal) expression);
    }

    // one reference of a variable: "a"
    if (expression instanceof JmlSingleNameReference) {
      return parseJmlSingleReference((JmlSingleNameReference) expression);
    }



    // \result is the result reference
//    if (expression instanceof JmlResultReference) return scope.getCurrentReturnVariable();

    // "\old(...)"
    if (expression instanceof JmlOldExpression) {
      return visitOldExpression((JmlOldExpression) expression);
    }

    // "some.other"
    if (expression instanceof JmlQualifiedNameReference) {
      return visitJmlQualifiedNameReference((JmlQualifiedNameReference) expression);
    }

    // "array[index]"
    if (expression instanceof JmlArrayReference) {
      return visitJmlArrayReference((JmlArrayReference) expression);
    }

    // "({\forall | \exists | \sum} boundVarDeclarations; rangeExpression; body)"
    if (expression instanceof JmlQuantifiedExpression) {
      return visitJmlQuantifiedExpression((JmlQuantifiedExpression) expression);
    }

    // "method()", "other.method()"
    if (expression instanceof JmlMessageSend) {
      return visitJmlMessageSend((JmlMessageSend) expression);
    }

    // expressions with operators: a + b, a ? b : c, !a ...
    if (expression instanceof OperatorExpression) {
      return parseOperatorExpression((OperatorExpression) expression);
    }

    return super.parseExpression(expression);
  }

  private Expr parseThisReference(ThisReference thisExpression) {
    throw new UnsupportedJMLExpression(thisExpression);
  }

  public Expr parseLiteral(Literal literalExpression) {
    // literals can be translated directly
    if (literalExpression instanceof IntLiteral)
      return ctx.mkInt(((IntLiteral) literalExpression).value);

    if (literalExpression instanceof DoubleLiteral) {
      double value = ((DoubleLiteral) literalExpression).constant.doubleValue();
      return ctx.mkFPToReal(ctx.mkFP(value, ctx.mkFPSortDouble()));
    }

    if (literalExpression instanceof TrueLiteral)
      return ctx.mkTrue();

    if (literalExpression instanceof FalseLiteral)
      return ctx.mkFalse();

    throw new UnsupportedJMLExpression(literalExpression);
  }

  public Expr parseOperatorExpression(OperatorExpression operatorExpression) {
    // !a ...
    if (operatorExpression instanceof UnaryExpression) {
      return parseUnaryExpression((UnaryExpression) operatorExpression);
    }

    // expressions like addition, modulo, and, or, ...
    if (operatorExpression instanceof BinaryExpression) {
      return parseBinaryExpression((BinaryExpression) operatorExpression);
    }

    if (operatorExpression instanceof ConditionalExpression) {
      return parseConditionalExpression((ConditionalExpression) operatorExpression);
    }

    throw new UnsupportedJMLExpression(operatorExpression);
  }

  public Expr parseUnaryExpression(UnaryExpression unaryExpression) {
    Expr expr = parseExpression(unaryExpression.expression);

    throw new UnsupportedJMLExpression(unaryExpression);
  }

  /**
   * Visit every kind of binary expression. Note, that bitwise operators are translated like their
   * logical pendant.
   *
   * @return e Z3 expression that uses the correct operator
   */
  public Expr parseBinaryExpression(BinaryExpression binaryExpression) {
    // translate expressions from both operands
    Expr left = parseExpression(binaryExpression.left);
    Expr right = parseExpression(binaryExpression.right);

    // get operator value and construct corresponding Z3 expression
    String s = binaryExpression.operatorToString();



    if (s.equals("&&") || s.equals("&")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return ctx.mkAnd((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArgumentsExpression(binaryExpression);
    }

    if (s.equals("||") || s.equals("|")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return ctx.mkOr((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArgumentsExpression(binaryExpression);
    }

    //TODO: Add WrongJMLArgumentsExpression to all cases
    if (s.equals("<") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkLt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("<=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkLe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkGt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkGe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("^") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return ctx.mkXor((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("/") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkDiv((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("-") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkSub((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("+") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkAdd((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("*") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return ctx.mkMul((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("%") && left instanceof IntExpr && right instanceof IntExpr) {
      return ctx.mkMod((IntExpr) left, (IntExpr) right);
    }

    /* if values need to be set, this point is used as not all equality operators are only used
    for equality constraints
    */
    if (left != null && right != null && (s.equals("<==>") || s.equals("=") || s.equals("=="))) {
      // set result expression for current scope
//      if (binaryExpression.left instanceof JmlResultReference) {
//        scope.setCurrentReturnExpression(right);
//      }
//
//      // set array size
//      else if (left instanceof SeqExpr && right instanceof IntExpr) {
//        //TODO: check this
//        InternalVar arr = scope.getClassVariable(left.getString());
//        if (arr instanceof InternalArray) {
//          ((InternalArray) arr)
//              .setSize(new IntegerValueVisitor().visitExpression(binaryExpression.right, scope));
//          return ctx.mkTrue();
//        }
//      }
      return ctx.mkEq(left, right);
    }

    if (s.equals("==>") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return ctx.mkImplies((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("<==") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return ctx.mkImplies((BoolExpr) right, (BoolExpr) left);
    }

    if (left != null && right != null && (s.equals("<=!=>") || s.equals("!=")))
      return ctx.mkNot(ctx.mkEq(left, right));

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
  public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
    String variableName = String.valueOf(jmlSingleNameReference.token);
    Expr cons = localVariables.get(variableName);

    if (cons == null) {
      throw new WrongJMLArgumentsExpression(jmlSingleNameReference);
    }

    return cons;
  }

  /**
   * Visits {@code \old(...)} expressions and substitutes every occurring variable with its prestate
   * Z3 constant.
   *
   * @return expression where every occurrence of a state variable is substituted with the variable
   *     depicting the old state
   */
  public Expr visitOldExpression(JmlOldExpression jmlOldExpression) {
//    // translate the whole expression inside \old(...)
//    Expr subExpr = parseExpression(jmlOldExpression.expression);
//
//    /*
//    Gather both prestate and poststate constants
//     */
//    int varSize = scope.getClassVariables().size();
//    Expr[] newVars = new Expr[varSize];
//    Expr[] oldVars = new Expr[varSize];
//
//    newVars =
//        scope.getClassVariables().values().stream()
//            .map(InternalVar::getNewValue)
//            .collect(Collectors.toList())
//            .toArray(newVars);
//
//    oldVars =
//        scope.getClassVariables().values().stream()
//            .map(InternalVar::getOldValue)
//            .collect(Collectors.toList())
//            .toArray(oldVars);
//
//    // substitute all occurrences of poststate variables with the prestate ones
//    return subExpr.substitute(newVars, oldVars);
    return null;
  }

  public Expr parseConditionalExpression(ConditionalExpression conditionalExpression) {
    Expr cond = parseExpression(conditionalExpression.condition);
    Expr thenBranch = parseExpression(conditionalExpression.valueIfTrue);
    Expr elseBranch = parseExpression(conditionalExpression.valueIfFalse);

    if (cond instanceof BoolExpr) {
      BoolExpr condBool = (BoolExpr) cond;

      return ctx.mkITE(condBool, thenBranch, elseBranch);
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
      JmlQualifiedNameReference jmlQualifiedNameReference) {

//    // in this case, it is class.variableName
//    if (jmlQualifiedNameReference.tokens.length == 2) {
//      String className = String.valueOf(jmlQualifiedNameReference.tokens[0]);
//      String varName = String.valueOf(jmlQualifiedNameReference.tokens[1]);
//
//      // the "other" variable needs to be used to depict the state relation of a merge constraint
//      if (className.equals("other") && scope.insideMergeFunction) {
//        return scope.getClassVariable(varName).getOtherValue();
//      }
//
//      // Get variable from scope -> in this case return new value or argument value
//      else if (className.equals("this")) {
//        // variable is some class variable
//        if (scope.getClassVariables().containsKey(varName)) {
//          return scope.getClassVariable(varName).getNewValue();
//        }
//        // variable is local variable
//        else if (scope.getLocalVariables().containsKey(varName)) {
//          return scope.getLocalVariable(varName);
//        }
//      }
//
      // array.length expected in constructor
//      else
//    if (scope.hasClassVariable(className) && varName.equals("length")) {
//        return ctx.mkString(className);
//    }


    throw new WrongJMLArgumentsExpression(jmlQualifiedNameReference);
  }

  /**
   * Visits select expressions like {@code array[index]}
   *
   * @return a Z3 select expressions or {@code null} if the translation did not succeed
   */
  public Expr visitJmlArrayReference(JmlArrayReference jmlArrayReference) {
    Expr array = parseExpression(jmlArrayReference.receiver);

    if (array instanceof ArrayExpr) {
      // get index expression
      Expr index = parseExpression(jmlArrayReference.position);
      return ctx.mkSelect((ArrayExpr) array, index);
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
      JmlQuantifiedExpression jmlQuantifiedExpression) {


    // boundVariables declaration: introduce new local scope
//    Map<String, Expr> newLocalVars = new HashMap<>(scope.getLocalVariables());
//    Expr[] boundConstants = new Expr[jmlQuantifiedExpression.boundVariables.length];

    int index = 0;
    String[] names = new String[jmlQuantifiedExpression.boundVariables.length];
    Expr[] consts = new Expr[jmlQuantifiedExpression.boundVariables.length];
    for (LocalDeclaration localDeclaration : jmlQuantifiedExpression.boundVariables) {
      names[index] = String.valueOf(localDeclaration.name);
      consts[index] = ctx.mkFreshConst(names[index], Z3Utils.typeReferenceToSort(ctx, localDeclaration.type));
      index++;
    }

    Expr quantExpr = withLocalVariables(names, consts, () -> {
      // get range and body expression
      Expr rangeExpr = parseExpression(jmlQuantifiedExpression.range);
      Expr bodyExpr = parseExpression(jmlQuantifiedExpression.body);

      //quantifier operator as string
      String quantifier = jmlQuantifiedExpression.quantifier.lexeme;

      // this applies to \forall and \exists expressions
      if (quantifier.equals(JmlQuantifier.EXISTS) || quantifier.equals(JmlQuantifier.FORALL)) {
        if (rangeExpr instanceof  BoolExpr && bodyExpr instanceof BoolExpr) {
          // range ==> body
          BoolExpr finalBodyExpr = ctx.mkImplies((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);

          boolean isForall = quantifier.equals(JmlQuantifier.FORALL);

          // quantifier: forall or exists
          Expr quantifiedExpr =
                  ctx.mkQuantifier(
                          isForall, //decide whether to create forall or exists quantifier
                          consts,
                          finalBodyExpr,
                          1,
                          null,
                          null,
                          ctx.mkSymbol("Q_" + getFreshId()),
                          ctx.mkSymbol("Sk_" + getFreshId()));

          return quantifiedExpr;
        }

        return null;
      }

      // this applies to \sum expressions
      if (quantifier.equals(JmlQuantifier.SUM)) {
        // NOTE: Summation always (!) start at i = 0, and increase i in every step by 1.
        System.err.println("Warning! \\sum only supports sums starting at 0.");

        if (jmlQuantifiedExpression.boundVariables.length != 1) {
          throw new WrongJMLArgumentsExpression(jmlQuantifiedExpression);
        }

        if (bodyExpr instanceof IntExpr) {
          Expr<IntSort> forBodyExpr = ctx.mkITE(rangeExpr, (IntExpr) bodyExpr, ctx.mkInt(0));
          IntExpr ret = ctx.mkInt(0);
          for (int i = 0; i < 20; i++) {

            ret = (IntExpr) ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], ctx.mkInt(i)));
          }
          return ret;
        } else if (bodyExpr instanceof RealExpr) {
          Expr<RealSort> forBodyExpr = ctx.mkITE(rangeExpr, (RealExpr) bodyExpr, ctx.mkReal(0));
          RealExpr ret = ctx.mkReal(0);
          for (int i = 0; i < 20; i++) {
            ret = (RealExpr) ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], ctx.mkInt(i)));
          }
          return ret;
        }
      }
      return null;
    });

    if (quantExpr == null) {
      throw new UnsupportedJMLExpression(jmlQuantifiedExpression);
    }

    return quantExpr;
  }


  public Expr visitJmlFieldReference(JmlFieldReference fieldReference) {
    throw new UnsupportedJMLExpression(fieldReference);
  }

  /**
   * Visits method call like {@code getValue()} or {@code other.getValue()}.
   *
   * @return the result expression of the called method if it has one, {@code null} otherwise
   */
  public Expr visitJmlMessageSend(JmlMessageSend jmlMessageSend) {
//
//    Expr methodReturnValue = scope.getReturnValue(String.valueOf(jmlMessageSend.selector));
//
//    if (methodReturnValue != null) {
//      // now distinguish between this and other -> check if its a this reference
//      if (jmlMessageSend.receiver instanceof ThisReference) {
//        return methodReturnValue;
//      } else {
//        // only method calls within the same class supported
//        int varSize = scope.getClassVariables().size();
//        Expr[] newVars = new Expr[varSize];
//        Expr[] otherVars = new Expr[varSize];
//        newVars =
//            scope.getClassVariables().values().stream()
//                .map(InternalVar::getNewValue)
//                .collect(Collectors.toList())
//                .toArray(newVars);
//        otherVars =
//            scope.getClassVariables().values().stream()
//                .map(InternalVar::getOtherValue)
//                .collect(Collectors.toList())
//                .toArray(otherVars);
//        return methodReturnValue.substitute(newVars, otherVars);
//      }
//    }

    throw new WrongJMLArgumentsExpression(jmlMessageSend);
  }

  /*
   ***************************************************************************************************************
   **************************************** Statements, called separately ****************************************
   ***************************************************************************************************************
   */


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
        BoolExpr res = ctx.mkTrue();
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
          res = ctx.mkAnd(res, ctx.mkEq(newVars[i], oldVars[i]));
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
      BoolExpr resultingPostCondition = ctx.mkTrue();

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
              ctx.mkAnd(
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
              ctx.mkAnd(
                  resultingPostCondition,
                  InternalArray.sameFields(
                      ((InternalArray) notChanging).getOldValue(),
                      ((InternalArray) notChanging).getNewValue(),
                      ((InternalArray) notChanging).getSize()));
        } else {
          resultingPostCondition =
              ctx.mkAnd(
                  resultingPostCondition,
                  ctx.mkEq(notChanging.getOldValue(), notChanging.getNewValue()));
        }
      }

      return resultingPostCondition;
    }

    throw new IllegalArgumentException(jmlAssignableClause.toString());
  }

  protected <T> T withLocalVariable(String varName, Expr varExpr, Supplier<T> f) {
    Expr prev = localVariables.put(varName, varExpr);

    T result = null;

    try {
      result = f.get();
    } finally {
      if (prev == null) {
        localVariables.remove(varName);
      } else {
        localVariables.put(varName, prev);
      }
    }

    return result;
  }

  protected <T> T withLocalVariables(String[] varName, Expr[] varExpr, Supplier<T> f) {
    if (varName.length != varExpr.length)
      throw new IllegalArgumentException("ranges of arrays do not match");

    Expr[] prev = new Expr[varName.length];
    for (int i = 0; i < varName.length; i++) {
      prev[i] = localVariables.put(varName[i], varExpr[i]);
    }

    T result = null;
    try {
      result = f.get();
    } finally {
      for (int i = 0; i < varName.length; i++) {
        if (prev[i] == null) {
          localVariables.remove(varName[i]);
        } else {
          localVariables.put(varName[i], prev[i]);
        }
      }
    }

    return result;
  }
}
