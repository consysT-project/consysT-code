package de.tuda.stg.consys.invariants.subset.parser;

import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.*;

import java.util.Arrays;
import java.util.Map;
import java.util.function.Supplier;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
@SuppressWarnings("rawtypes")
public class BaseExpressionParser extends ExpressionParser {

  // The z3 context used for creating expressions
  protected final ProgramModel model;
  // Local variables from jml quantifiers.
  private final Map<String, Expr> localVariables = Maps.newHashMap();


  public BaseExpressionParser(ProgramModel model) {
    this.model = model;
  }

  /**
   * This method calls the correct visitXYZ(...) method for a given JML expression
   *
   * @param expression the expression to be visited
   * @return the corresponding Z3 expression
   */
  @Override
  public Expr parseExpression(Expression expression) {

    if (expression == null) {
      Logger.warn("expression was null and was converted to `true`");
      return model.ctx.mkTrue();
    }

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

    // method calls
    if (expression instanceof JmlMessageSend) {
      return parseJmlMessageSend((JmlMessageSend) expression);
    }

    return super.parseExpression(expression);
  }

  public Expr parseLiteral(Literal literalExpression) {
    // literals can be translated directly
    if (literalExpression instanceof IntLiteral)
      return model.ctx.mkInt(((IntLiteral) literalExpression).value);

    if (literalExpression instanceof DoubleLiteral) {
      double value = ((DoubleLiteral) literalExpression).constant.doubleValue();
      return model.ctx.mkFPToReal(model.ctx.mkFP(value, model.ctx.mkFPSortDouble()));
    }

    if (literalExpression instanceof TrueLiteral)
      return model.ctx.mkTrue();

    if (literalExpression instanceof FalseLiteral)
      return model.ctx.mkFalse();

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
        return model.ctx.mkAnd((BoolExpr) left, (BoolExpr) right);
      }
      throw new UnsupportedJMLExpression(binaryExpression);
    }

    if (s.equals("||") || s.equals("|")) {
      if (left instanceof BoolExpr && right instanceof BoolExpr) {
        return model.ctx.mkOr((BoolExpr) left, (BoolExpr) right);
      }
      throw new UnsupportedJMLExpression(binaryExpression);
    }

    if (s.equals("<") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkLt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("<=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkLe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkGt((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals(">=") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkGe((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("^") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return model.ctx.mkXor((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("/") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkDiv((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("-") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkSub((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("+") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkAdd((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("*") && left instanceof ArithExpr && right instanceof ArithExpr) {
      return model.ctx.mkMul((ArithExpr) left, (ArithExpr) right);
    }
    if (s.equals("%") && left instanceof IntExpr && right instanceof IntExpr) {
      return model.ctx.mkMod((IntExpr) left, (IntExpr) right);
    }

    /* if values need to be set, this point is used as not all equality operators are only used
    for equality constraints
    */
    if (left != null && right != null && (s.equals("<==>") || s.equals("=") || s.equals("=="))) {
      return model.ctx.mkEq(left, right);
    }

    if (s.equals("==>") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return model.ctx.mkImplies((BoolExpr) left, (BoolExpr) right);
    }
    if (s.equals("<==") && left instanceof BoolExpr && right instanceof BoolExpr) {
      return model.ctx.mkImplies((BoolExpr) right, (BoolExpr) left);
    }

    if (left != null && right != null && (s.equals("<=!=>") || s.equals("!=")))
      return model.ctx.mkNot(model.ctx.mkEq(left, right));

    throw new UnsupportedJMLExpression(binaryExpression);
  }

  public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
    String variableName = String.valueOf(jmlSingleNameReference.token);
    Expr cons = localVariables.get(variableName);

    if (cons == null) {
      throw new UnsupportedJMLExpression(jmlSingleNameReference);
    }

    return cons;
  }


  public Expr parseConditionalExpression(ConditionalExpression conditionalExpression) {
    Expr cond = parseExpression(conditionalExpression.condition);
    Expr thenBranch = parseExpression(conditionalExpression.valueIfTrue);
    Expr elseBranch = parseExpression(conditionalExpression.valueIfFalse);

    if (cond instanceof BoolExpr) {
      BoolExpr condBool = (BoolExpr) cond;
      return model.ctx.mkITE(condBool, thenBranch, elseBranch);
    }

    throw new UnsupportedJMLExpression(conditionalExpression);

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
      return model.ctx.mkSelect((ArrayExpr) array, index);
    }

    throw new UnsupportedJMLExpression(jmlArrayReference);
  }

  public Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend) {
    // Resolve some basic functions for convenient usage in constraints
    var methodName = String.valueOf(jmlMessageSend.selector);

    var methodBinding = jmlMessageSend.binding;

    // The cases are categorized by the classes in which they are defined:
    // java.lang.Object
    if (JDTUtils.methodMatchesSignature(methodBinding, false,"java.lang.Object", "equals", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver);
      var argExpr = parseExpression(jmlMessageSend.arguments[0]);
      return model.ctx.mkEq(receiverExpr, argExpr);
    }
    // java.util.Map
    else if (JDTUtils.methodMatchesSignature(methodBinding, false, "java.util.Map", "get", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver);
      var argExpr = parseExpression(jmlMessageSend.arguments[0]);
      return model.ctx.mkSelect(receiverExpr, argExpr);
    }
    // java.math.BigInteger
    else if (JDTUtils.methodMatchesSignature(methodBinding, false, "java.math.BigInteger", "add", "java.math.BigInteger")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver);
      var argExpr = parseExpression(jmlMessageSend.arguments[0]);

      return model.ctx.mkAdd(receiverExpr, argExpr);
    }  else if (JDTUtils.methodMatchesSignature(methodBinding, true, "java.math.BigInteger", "valueOf", "long")) {
      var argExpr = parseExpression(jmlMessageSend.arguments[0]);
      return argExpr;
    }
    // java
    else if (JDTUtils.methodMatchesSignature(methodBinding, true, "java.lang.Math", "max", "int", "int")) {
      var arg1Expr = parseExpression(jmlMessageSend.arguments[0]);
      var arg2Expr = parseExpression(jmlMessageSend.arguments[1]);

      return model.ctx.mkITE(
              model.ctx.mkGe(arg1Expr, arg2Expr),
              arg1Expr, arg2Expr
      );
    } else if (JDTUtils.methodMatchesSignature(methodBinding, true, "java.lang.Math", "min", "int", "int")) {
      var arg1Expr = parseExpression(jmlMessageSend.arguments[0]);
      var arg2Expr = parseExpression(jmlMessageSend.arguments[1]);

      return model.ctx.mkITE(
              model.ctx.mkLe(arg1Expr, arg2Expr),
              arg1Expr, arg2Expr
      );
    }

    /* Handle call to method from a class in the data model */
    var receiverExpr = parseExpression(jmlMessageSend.receiver);
    var declaringClassModel = model.getModelForClass(methodBinding.declaringClass)
            .orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend, "class " + String.valueOf(methodBinding.declaringClass.shortReadableName()) + " not in data model"));

    var methodModel = declaringClassModel.getMethod(methodBinding)
            .orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend, "method not available in " + declaringClassModel.getClassName()));

    if (!methodModel.isZ3Usable())
      throw new UnsupportedJMLExpression(jmlMessageSend, "method is not usable in Z3");

    final Expr[] argExprs;
    if (jmlMessageSend.arguments == null) {
      argExprs = new Expr[0];
    } else {
      argExprs = Arrays.stream(jmlMessageSend.arguments)
              .map(this::parseExpression)
              .toArray(Expr[]::new);
    }

    var mbApply = methodModel.makeApply(receiverExpr, argExprs);

    if (mbApply.isEmpty()) throw new UnsupportedJMLExpression(jmlMessageSend);

    return mbApply.get();
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
      consts[index] = model.ctx.mkFreshConst(names[index], model.types.typeFor(localDeclaration.type).toSort());
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

          final BoolExpr finalBodyExpr;
          if (quantifier.equals(JmlQuantifier.FORALL)) {
            // \forall x. range ==> body
            finalBodyExpr = model.ctx.mkImplies((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);
          } else {
            // \exists x. range && body
            finalBodyExpr = model.ctx.mkAnd((BoolExpr) rangeExpr, (BoolExpr) bodyExpr);
          }


          boolean isForall = quantifier.equals(JmlQuantifier.FORALL);

          // quantifier: forall or exists
          Expr quantifiedExpr =
                  model.ctx.mkQuantifier(
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
        Logger.warn("\\sum only supports sums in range from -2000 to 2000");

        if (jmlQuantifiedExpression.boundVariables.length != 1) {
          throw new UnsupportedJMLExpression(jmlQuantifiedExpression);
        }

        if (bodyExpr instanceof IntExpr) {
          Expr<IntSort> forBodyExpr = model.ctx.mkITE(rangeExpr, (IntExpr) bodyExpr, model.ctx.mkInt(0));
          IntExpr ret = model.ctx.mkInt(0);
          for (int i = -2000; i <= 2000; i++) {
            ret = (IntExpr) model.ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], model.ctx.mkInt(i)));
          }
          return ret;
        } else if (bodyExpr instanceof RealExpr) {
          Expr<RealSort> forBodyExpr = model.ctx.mkITE(rangeExpr, (RealExpr) bodyExpr, model.ctx.mkReal(0));
          RealExpr ret = model.ctx.mkReal(0);
          for (int i = 0; i < 20; i++) {
            ret = (RealExpr) model.ctx.mkAdd(ret, forBodyExpr.substitute(consts[0], model.ctx.mkInt(i)));
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
