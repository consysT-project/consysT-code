package de.tuda.stg.consys.invariants.subset.parser;

import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArguments;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.JmlArrayReference;
import org.jmlspecs.jml4.ast.JmlQuantifiedExpression;
import org.jmlspecs.jml4.ast.JmlQuantifier;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

import java.util.Map;
import java.util.function.Supplier;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
@SuppressWarnings("rawtypes")
public class BaseExpressionParser extends ExpressionParser {

  // The z3 context used for creating expressions
  protected final Z3Binding smt;
  // Local variables from jml quantifiers.
  private final Map<String, Expr> localVariables = Maps.newHashMap();


  public BaseExpressionParser(Z3Binding smt) {
    this.smt = smt;
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

      // "array[index]"
    if (expression instanceof JmlArrayReference) {
      return visitJmlArrayReference((JmlArrayReference) expression);
    }

    // "({\forall | \exists | \sum} boundVarDeclarations; rangeExpression; body)"
    if (expression instanceof JmlQuantifiedExpression) {
      return visitJmlQuantifiedExpression((JmlQuantifiedExpression) expression);
    }

    // expressions with operators: a + b, a ? b : c, !a ...
    if (expression instanceof OperatorExpression) {
      return parseOperatorExpression((OperatorExpression) expression);
    }

    return super.parseExpression(expression);
  }

  public Expr parseLiteral(Literal literalExpression) {
    // literals can be translated directly
    if (literalExpression instanceof IntLiteral)
      return smt.ctx.mkInt(((IntLiteral) literalExpression).value);

    if (literalExpression instanceof DoubleLiteral) {
      double value = ((DoubleLiteral) literalExpression).constant.doubleValue();
      return smt.ctx.mkFPToReal(smt.ctx.mkFP(value, smt.ctx.mkFPSortDouble()));
    }

    if (literalExpression instanceof TrueLiteral)
      return smt.ctx.mkTrue();

    if (literalExpression instanceof FalseLiteral)
      return smt.ctx.mkFalse();

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
        return smt.ctx.mkAnd((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArguments(binaryExpression);
    }

    if (s.equals("||") || s.equals("|")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return smt.ctx.mkOr((BoolExpr) left, (BoolExpr) right);
      }
      throw new WrongJMLArguments(binaryExpression);
    }

    if (s.equals("<") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkLt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("<=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkLe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkGt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkGe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("^") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return smt.ctx.mkXor((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("/") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkDiv((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("-") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkSub((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("+") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkAdd((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("*") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return smt.ctx.mkMul((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("%") && left instanceof IntExpr && right instanceof IntExpr) {
      return smt.ctx.mkMod((IntExpr) left, (IntExpr) right);
    }

    /* if values need to be set, this point is used as not all equality operators are only used
    for equality constraints
    */
    if (left != null && right != null && (s.equals("<==>") || s.equals("=") || s.equals("=="))) {
      return smt.ctx.mkEq(left, right);
    }

    if (s.equals("==>") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return smt.ctx.mkImplies((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("<==") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return smt.ctx.mkImplies((BoolExpr) right, (BoolExpr) left);
    }

    if (left != null && right != null && (s.equals("<=!=>") || s.equals("!=")))
      return smt.ctx.mkNot(smt.ctx.mkEq(left, right));

    throw new UnsupportedJMLExpression(binaryExpression);
  }

  public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
    String variableName = String.valueOf(jmlSingleNameReference.token);
    Expr cons = localVariables.get(variableName);

    if (cons == null) {
      throw new WrongJMLArguments(jmlSingleNameReference);
    }

    return cons;
  }


  public Expr parseConditionalExpression(ConditionalExpression conditionalExpression) {
    Expr cond = parseExpression(conditionalExpression.condition);
    Expr thenBranch = parseExpression(conditionalExpression.valueIfTrue);
    Expr elseBranch = parseExpression(conditionalExpression.valueIfFalse);

    if (cond instanceof BoolExpr) {
      BoolExpr condBool = (BoolExpr) cond;

      return smt.ctx.mkITE(condBool, thenBranch, elseBranch);
    }

    throw new WrongJMLArguments(conditionalExpression);

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
      return smt.ctx.mkSelect((ArrayExpr) array, index);
    }

    throw new WrongJMLArguments(jmlArrayReference);
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
      consts[index] = smt.ctx.mkFreshConst(names[index], Z3Utils.typeReferenceToSort(smt.ctx, localDeclaration.type).orElseThrow());
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
          BoolExpr finalBodyExpr = smt.ctx.mkImplies((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);

          boolean isForall = quantifier.equals(JmlQuantifier.FORALL);

          // quantifier: forall or exists
          Expr quantifiedExpr =
                  smt.ctx.mkQuantifier(
                          isForall, //decide whether to create forall or exists quantifier
                          consts,
                          finalBodyExpr,
                          1,
                          null,
                          null,
                          null, //smt.ctx.mkSymbol("Q_" + getFreshId()),
                          null //smt.ctx.mkSymbol("Sk_" + getFreshId())
                  );

          return quantifiedExpr;
        }

        return null;
      }

      // this applies to \sum expressions
      if (quantifier.equals(JmlQuantifier.SUM)) {
        // NOTE: Summation always (!) start at i = 0, and increase i in every step by 1.
        System.err.println("Warning! \\sum only supports sums in range from -2000 to 2000.");

        if (jmlQuantifiedExpression.boundVariables.length != 1) {
          throw new WrongJMLArguments(jmlQuantifiedExpression);
        }

        if (bodyExpr instanceof IntExpr) {
          Expr<IntSort> forBodyExpr = smt.ctx.mkITE(rangeExpr, (IntExpr) bodyExpr, smt.ctx.mkInt(0));
          IntExpr ret = smt.ctx.mkInt(0);
          for (int i = -2000; i <= 2000; i++) {
            ret = (IntExpr) smt.ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], smt.ctx.mkInt(i)));
          }
          return ret;
        } else if (bodyExpr instanceof RealExpr) {
          Expr<RealSort> forBodyExpr = smt.ctx.mkITE(rangeExpr, (RealExpr) bodyExpr, smt.ctx.mkReal(0));
          RealExpr ret = smt.ctx.mkReal(0);
          for (int i = 0; i < 20; i++) {
            ret = (RealExpr) smt.ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], smt.ctx.mkInt(i)));
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
