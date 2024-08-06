package de.tuda.stg.consys.invariants.solver.subset.parser;

import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.solver.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.utils.InvariantUtils;
import de.tuda.stg.consys.logging.Logger;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.jmlspecs.jml4.ast.*;

import java.util.Arrays;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * This visitor class is used to translate JML expressions, local variable declarations and
 * assignable clauses to Z3 expressions
 */
@SuppressWarnings("rawtypes")
public class BaseExpressionParser extends ExpressionParser {


  // Local variables from jml quantifiers.
  private final Map<LocalVariableBinding, Expr> localVariables = Maps.newHashMap();

  private boolean allowStatefulMethodCalls = false;

  public BaseExpressionParser(ProgramModel model) {
    super(model);
  }

  @Override
  protected Expr parseArrayAllocationExpression(ArrayAllocationExpression arrayAllocationExpression, int depth) {
    var type = model.types.typeFor(arrayAllocationExpression.resolvedType);
    var sort = type.getSort().orElseThrow(() -> new UnsupportedJMLExpression(arrayAllocationExpression, "unsupported array type " + type));

    var arrayConst = model.ctx.mkFreshConst("array_new", sort);

    var init = arrayAllocationExpression.initializer;
    if (init != null) {
      Logger.warn("created constant array. The elements in that array may not change. Array: " + arrayAllocationExpression);
      for (int i = 0; i < init.expressions.length; i++) {
        var expr = parseExpression(init.expressions[i]);
        model.solver.add(
          model.ctx.mkEq(
                  model.ctx.mkSelect((ArrayExpr) arrayConst, model.ctx.mkInt(i)),
                  expr
          )
        );
      }
      return arrayConst;
    }

    return super.parseArrayAllocationExpression(arrayAllocationExpression, depth);
  }

  @Override
  protected Expr parseLiteral(Literal literalExpression, int depth) {
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

    if (literalExpression instanceof StringLiteral)
      return model.ctx.mkString(String.valueOf(literalExpression.constant.stringValue()));

    return parseLiteral(literalExpression, depth);
  }

  @Override
  protected Expr parseUnaryExpression(UnaryExpression unaryExpression, int depth) {
    Expr expr = parseExpression(unaryExpression.expression, depth + 1);
    if (expr != null) return expr;

    return super.parseUnaryExpression(unaryExpression, depth);
  }

  /**
   * Visit every kind of binary expression. Note, that bitwise operators are translated like their
   * logical pendant.
   *
   * @return e Z3 expression that uses the correct operator
   */
  @Override
  protected Expr parseBinaryExpression(BinaryExpression binaryExpression, int depth) {
    // translate expressions from both operands
    Expr left = parseExpression(binaryExpression.left, depth + 1);
    Expr right = parseExpression(binaryExpression.right, depth + 1);

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

    return super.parseOperatorExpression(binaryExpression, depth);
  }

  @Override
  protected Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference, int depth) {
    Expr cons = lookupLocalVariable(jmlSingleNameReference.localVariableBinding()).orElse(null);
    if (cons != null) {
      return cons;
    }

    return super.parseJmlSingleReference(jmlSingleNameReference, depth);
  }

  @Override
  protected Expr parseJmlQualifiedNameReference(JmlQualifiedNameReference jmlQualifiedNameReference, int depth) {
    String className = String.valueOf(jmlQualifiedNameReference.tokens[0]);
    String classField = String.valueOf(jmlQualifiedNameReference.tokens[1]);
    Expr cons = null;

    if(className.equals("BigInteger")) {
      if (classField.equals("ZERO"))
        cons = model.ctx.mkIntConst("0");
    }
    if (cons != null) {
      return cons;
    }

    if (jmlQualifiedNameReference.binding instanceof LocalVariableBinding) {
      var receiverBinding = (LocalVariableBinding) jmlQualifiedNameReference.binding;
      var receiverExpr = lookupLocalVariable(receiverBinding)
              .orElseThrow(() -> new UnsupportedJMLExpression(jmlQualifiedNameReference, "local variable not found"));

      var result = handleQualifiedName(jmlQualifiedNameReference, receiverExpr);

      return result;
    }

    return super.parseJmlQualifiedNameReference(jmlQualifiedNameReference, depth);

  }

  @Override
  protected Expr parseJmlFieldReference(JmlFieldReference fieldReference, int depth) {
    if (!(fieldReference.receiverType instanceof ReferenceBinding))
      return super.parseJmlFieldReference(fieldReference, depth);

    var mbClassModel = model.getClassModel((ReferenceBinding) fieldReference.receiverType);
    if (mbClassModel.isEmpty())
      return super.parseJmlFieldReference(fieldReference, depth);

    var classModel = mbClassModel.get();

    Expr receiver = parseExpression(fieldReference.receiver, depth + 1);

    var mbField = classModel.getField(fieldReference.fieldBinding());
    if (mbField.isEmpty())
      return super.parseJmlFieldReference(fieldReference, depth);

    var result = mbField.get().getAccessor().apply(receiver);
    return result;
  }

  @Override
  protected Expr parseConditionalExpression(ConditionalExpression conditionalExpression, int depth) {
    Expr cond = parseExpression(conditionalExpression.condition, depth + 1);
    Expr thenBranch = parseExpression(conditionalExpression.valueIfTrue, depth + 1);
    Expr elseBranch = parseExpression(conditionalExpression.valueIfFalse, depth + 1);

    if (cond instanceof BoolExpr) {
      BoolExpr condBool = (BoolExpr) cond;
      return model.ctx.mkITE(condBool, thenBranch, elseBranch);
    }

    return super.parseConditionalExpression(conditionalExpression, depth);
  }

  /**
   * Visits select expressions like {@code array[index]}
   *
   * @return a Z3 select expressions or {@code null} if the translation did not succeed
   */
  @Override
  protected Expr parseJmlArrayReference(JmlArrayReference jmlArrayReference, int depth) {
    Expr array = parseExpression(jmlArrayReference.receiver, depth + 1);

    if (array instanceof ArrayExpr) {
      // get index expression
      Expr index = parseExpression(jmlArrayReference.position, depth + 1);
      return model.ctx.mkSelect((ArrayExpr) array, index);
    }

//    model.ctx.mkTu

    return super.parseJmlArrayReference(jmlArrayReference, depth);
  }

  @Override
  protected Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend, int depth) {
    var receiverBinding = jmlMessageSend.actualReceiverType;
    var methodBinding = jmlMessageSend.binding;


    /* Handle call to method from a class in the data model */
    var maybeMethodModel = model
            .getClassModel(methodBinding.declaringClass)
            .flatMap(cls -> cls.getMethod(methodBinding));
    // If the method exists then handle it!
    if (maybeMethodModel.isPresent()) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var methodModel = maybeMethodModel.get();

      if (!methodModel.usableAsConstraint() || (!methodModel.isPure() && !allowStatefulMethodCalls))
        return super.parseJmlMessageSend(jmlMessageSend, depth);

      /* Create exprs for all arguments */
      final Expr[] argExprs;
      if (jmlMessageSend.arguments == null) {
        argExprs = new Expr[0];
      } else {
        argExprs = Arrays.stream(jmlMessageSend.arguments)
                .map(jmlExpr -> parseExpression(jmlExpr, depth + 1))
                .toArray(Expr[]::new);
      }

      /* if the method is in a stateful expression, and it is the top method, then create a state method instead */
      Expr methodInvocation;
      if (allowStatefulMethodCalls && depth == 0) {
        methodInvocation = methodModel.makeApplyReturnState(receiverExpr, argExprs)
                .orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend));
      } else {
        methodInvocation = methodModel.makeApplyReturnValue(receiverExpr, argExprs)
                .orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend));
      }
      return methodInvocation;
    }


    // The cases are categorized by the classes in which they are defined:
    // java.lang.Object
    if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false,"java.lang.Object", "equals", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkEq(receiverExpr, argExpr);
    }
    // java.util.Map
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Map", "get", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkSelect(receiverExpr, argExpr);
    }
    //Consys Arrays
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "de.tuda.stg.consys.invariants.lib.Array", "get", "int")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);

      var result = model.ctx.mkSelect(receiverExpr, argExpr);

      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "de.tuda.stg.consys.invariants.lib.Array", "set", "int", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var indexExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var valueExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      var result = model.ctx.mkStore(receiverExpr, indexExpr, valueExpr);

      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.SetUtils", "emptySet")) {
      var set1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var set2Expr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      //TODO: How to retrieve the type of set elements?
      throw new UnsupportedOperationException();
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.SetUtils", "union", "java.util.Set", "java.util.Set")) {
      var set1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var set2Expr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      var result = model.ctx.mkSetUnion(set1Expr, set2Expr);

      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.SetUtils", "in", "java.util.Set", "java.lang.Object")) {
      var set1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var elemExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      var result = model.ctx.mkSetMembership(elemExpr, set1Expr);
      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.SetUtils", "add", "java.util.Set", "java.lang.Object")) {
      var set1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var elemExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      var result = model.ctx.mkSetAdd(set1Expr, elemExpr);
      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.ArrayUtils", "update", "int[]", "int", "int")) {
      var arrExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var indexExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);
      var newValExpr = parseExpression(jmlMessageSend.arguments[2], depth + 1);

      var result = model.ctx.mkStore(arrExpr, indexExpr, newValExpr);
      return result;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "de.tuda.stg.consys.annotations.invariants.ArrayUtils", "update", "java.lang.Object[]", "int", "java.lang.Object")) {
      var arrExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var indexExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);
      var newValExpr = parseExpression(jmlMessageSend.arguments[2], depth + 1);

      var result = model.ctx.mkStore(arrExpr, indexExpr, newValExpr);
      return result;
    }
	// com.google.common.collect.Multimap
	else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "com.google.common.collect.Multimap", "isEmpty")) {
		var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
		var multimapSort = (ArraySort) receiverExpr.getSort();
		var internalCollectionSort = (ArraySort) multimapSort.getRange();
		var keySort = multimapSort.getDomain();
		var valueSort = internalCollectionSort.getDomain();

		var c = model.ctx;

		var k = c.mkFreshConst("k", keySort);
		var v = c.mkFreshConst("v", valueSort);

		var result = c.mkForall(new Expr[]{k, v},
				c.mkEq(c.mkSelect(c.mkSelect(receiverExpr, k), v), c.mkInt(0)),
				1, null, null, null, null);

		return result;
	} else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "com.google.common.collect.Multimap", "containsKey", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var multimapSort = (ArraySort) receiverExpr.getSort();
      var internalCollectionSort = (ArraySort) multimapSort.getRange();
      var valueSort = internalCollectionSort.getDomain();
      var c = model.ctx;
      var v = c.mkFreshConst("v", valueSort);
      var result = c.mkExists(new Expr[]{v},
              c.mkGt(c.mkSelect(c.mkSelect(receiverExpr, argExpr), v), c.mkInt(0)),
              1, null, null, null, null);

      return result;
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "com.google.common.collect.Multimap", "containsValue", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var multimapSort = (ArraySort) receiverExpr.getSort();
      var internalCollectionSort = (ArraySort) multimapSort.getRange();
      var keySort = multimapSort.getDomain();
      var c = model.ctx;
      var k = c.mkFreshConst("k", keySort);
      var result = c.mkExists(new Expr[]{k},
              c.mkGt(c.mkSelect(c.mkSelect(receiverExpr, k), argExpr), c.mkInt(0)),
              1, null, null, null, null);

      return result;
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "com.google.common.collect.Multimap", "get", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var c = model.ctx;
      var result = c.mkSelect(receiverExpr, argExpr);

      return result;
    }
    // java.util.Set
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Set", "isEmpty")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      ArraySort sort = (ArraySort) receiverExpr.getSort();
//      var e = model.ctx.mkFreshConst("e", sort.getDomain());
//      return model.ctx.mkForall(new Expr[]{e}, model.ctx.mkNot(model.ctx.mkSetMembership(e, receiverExpr)), 1, null, null, null, null);
      return model.ctx.mkEq(receiverExpr, model.ctx.mkEmptySet(sort.getDomain()));
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Set", "contains", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkSetMembership(argExpr, receiverExpr);
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Set", "containsAll", "java.util.Collection")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkSetSubset(argExpr, receiverExpr);
    }


    // java.util.Map
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Map", "put", "java.lang.Object", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var indexExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var valueExpr = parseExpression(jmlMessageSend.arguments[1], depth + 1);
      return model.ctx.mkStore(receiverExpr, indexExpr, valueExpr);
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Map", "get", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkSelect(receiverExpr, argExpr);
    }




    // java.util.Collection
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Collection", "isEmpty")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      ArraySort sort = (ArraySort) receiverExpr.getSort();
      var e = model.ctx.mkFreshConst("e", sort.getDomain());
      return model.ctx.mkForall(new Expr[]{e},
              model.ctx.mkEq(model.ctx.mkSelect(receiverExpr, e), model.ctx.mkInt(0)),
              1, null, null, null, null);
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.util.Collection", "contains", "java.lang.Object")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkGt(model.ctx.mkSelect(receiverExpr, argExpr), model.ctx.mkInt(0));
    }
    // java.math.BigInteger
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.math.BigInteger", "add", "java.math.BigInteger")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkAdd(receiverExpr, argExpr);
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.math.BigInteger", "subtract", "java.math.BigInteger")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return model.ctx.mkSub(receiverExpr, argExpr);
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "java.math.BigInteger", "valueOf", "long")) {
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      return argExpr;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.math.BigInteger", "intValue")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      return receiverExpr;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.math.BigInteger", "hashCode")) {
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      return receiverExpr;
    }
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, false, "java.math.BigInteger", "compareTo", "java.math.BigInteger")) {
      // This method is not working correctly for equal situation. Please use equals for that purpose also.
      var receiverExpr = parseExpression(jmlMessageSend.receiver, depth + 1);
      var argExpr = parseExpression(jmlMessageSend.arguments[0], depth + 1);

      return model.ctx.mkITE(
              model.ctx.mkEq(receiverExpr, argExpr),
              model.ctx.mkInt(0),
              model.ctx.mkITE(
                      model.ctx.mkGe(argExpr, receiverExpr),
                      model.ctx.mkInt(-1), model.ctx.mkInt(1)
              )
      );
    }
    // Math
    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "java.lang.Math", "max", "int", "int")) {
      var arg1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var arg2Expr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      return model.ctx.mkITE(
              model.ctx.mkGe(arg1Expr, arg2Expr),
              arg1Expr, arg2Expr
      );
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, "java.lang.Math", "min", "int", "int")) {
      var arg1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var arg2Expr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      return model.ctx.mkITE(
              model.ctx.mkLe(arg1Expr, arg2Expr),
              arg1Expr, arg2Expr
      );
    }
    // System methods




    else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, InvariantUtils.class.getName(), "replicaId")) {
      return model.ctx.mkInt(model.config.SYSTEM__REPLICA_ID);

    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, InvariantUtils.class.getName(), "replica")) {
      return model.ctx.mkString(model.config.SYSTEM__REPLICA);

    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, InvariantUtils.class.getName(), "numOfReplicas")) {
      return model.ctx.mkInt(model.config.SYSTEM__NUM_OF_REPLICAS);

    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, InvariantUtils.class.getName(), "object", "java.lang.Class", "java.lang.Object[]")) {
      var classArg = jmlMessageSend.arguments[0];

      if (!(classArg instanceof ClassLiteralAccess)) {
        throw new UnsupportedJMLExpression(jmlMessageSend.arguments[0], "the method <object> expects a class literal as its first argument.");
      }

      var classLiteral = (ClassLiteralAccess) classArg;
      var typeModel = model.types.typeFor(classLiteral.targetType);
      var typeSort = typeModel.getSort().orElseThrow();

      if (!(typeSort instanceof TupleSort)) {
        throw new UnsupportedJMLExpression(jmlMessageSend.arguments[0], "the class has no Z3 interpretation (missing @DataModel?).");
      }

      var objectSort = (TupleSort) typeSort;
      var constrDecl = objectSort.mkDecl();

      var argExprs = new Expr[jmlMessageSend.arguments.length - 1];

      for (int i = 0; i < argExprs.length; i++) {
        argExprs[i] = parseExpression(jmlMessageSend.arguments[i + 1], depth + 1);
      }

      var expr = constrDecl.apply(argExprs);

      return expr;
    } else if (JDTUtils.methodMatchesSignature(receiverBinding, methodBinding, true, InvariantUtils.class.getName(), "arrayMax", "int[]", "int[]")) {
      var arg1Expr = parseExpression(jmlMessageSend.arguments[0], depth + 1);
      var arg2Expr = parseExpression(jmlMessageSend.arguments[1], depth + 1);

      var arrayConst = model.ctx.mkFreshConst("arrayMax", model.ctx.mkArraySort(model.ctx.getIntSort(), model.ctx.getIntSort()));

      var iConst = model.ctx.mkFreshConst("i", model.ctx.getIntSort());

      var assertion = model.ctx.mkForall(
              new Expr[] { iConst },
              model.ctx.mkEq(
                      model.ctx.mkSelect(arrayConst, iConst),
                      model.ctx.mkITE(
                        model.ctx.mkGe(model.ctx.mkSelect(arg1Expr, iConst), model.ctx.mkSelect(arg2Expr, iConst)),
                        model.ctx.mkSelect(arg1Expr, iConst),
                        model.ctx.mkSelect(arg2Expr, iConst)
                      )
              ),
              0, null, null, null, null
      );

      model.solver.add(assertion);

      return arrayConst;
    }





    return super.parseJmlMessageSend(jmlMessageSend, depth);
  }


  @Override
  protected Expr parseCastExpression(CastExpression expression, int depth) {
    var inner = expression.expression;
    return parseExpression(inner, depth + 1);
  }

  /**
   * Visits quantified expressions and translates universal/existential quantification directly to
   * Z3 quantifiers. Sum quantification is only supported if it is applied on an array reference
   * with range constraints.
   *
   * @return
   */
  @Override
  protected Expr parseJmlQuantifiedExpression(JmlQuantifiedExpression jmlQuantifiedExpression, int depth) {
    int index = 0;
    LocalVariableBinding[] vars = new LocalVariableBinding[jmlQuantifiedExpression.boundVariables.length];
    Expr[] consts = new Expr[jmlQuantifiedExpression.boundVariables.length];
    for (LocalDeclaration localDeclaration : jmlQuantifiedExpression.boundVariables) {
      vars[index] = localDeclaration.binding;
      consts[index] = mkFreshLocalVar(vars[index]);
      index++;
    }

    Expr quantExpr = withLocalVariables(vars, consts, () -> {

      // get range and body expression
      Expr rangeExpr = parseExpression(jmlQuantifiedExpression.range, depth + 1);
      Expr bodyExpr = parseExpression(jmlQuantifiedExpression.body, depth + 1);

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
//        Logger.warn("\\sum only supports sums in range from -2000 to 2000");

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

    if (quantExpr != null) {
      return quantExpr;
    }

    return super.parseJmlQuantifiedExpression(jmlQuantifiedExpression, depth);
  }

  protected <T> T withLocalVariable(LocalVariableBinding varBinding, Expr varExpr, Supplier<T> f) {
    Expr prev = localVariables.put(varBinding, varExpr);

    T result = null;

    try {
      result = f.get();
    } finally {
      if (prev == null) {
        localVariables.remove(varBinding);
      } else {
        localVariables.put(varBinding, prev);
      }
    }

    return result;
  }

  protected <T> T withLocalVariables(LocalVariableBinding[] varBinding, Expr[] varExpr, Supplier<T> f) {
    if (varBinding.length != varExpr.length)
      throw new IllegalArgumentException("ranges of arrays do not match");

    Expr[] prev = new Expr[varBinding.length];
    for (int i = 0; i < varBinding.length; i++) {
      prev[i] = localVariables.put(varBinding[i], varExpr[i]);
    }

    T result = null;
    try {
      result = f.get();
    } finally {
      for (int i = 0; i < varBinding.length; i++) {
        if (prev[i] == null) {
          localVariables.remove(varBinding[i]);
        } else {
          localVariables.put(varBinding[i], prev[i]);
        }
      }
    }

    return result;
  }

  protected <T> T withStatefulMethods(Supplier<T> f) {
    boolean prev = this.allowStatefulMethodCalls;
    allowStatefulMethodCalls = true;

    T result = null;
    try {
      result = f.get();
    } finally {
      allowStatefulMethodCalls = prev;
    }

    return result;
  }

  protected Expr mkFreshLocalVar(LocalVariableBinding binding) {
    return model.ctx.mkFreshConst(String.valueOf(binding.name), model.types.typeFor(binding.type).toSort());
  }

  protected void addLocalVariable(LocalVariableBinding binding, Expr expr) {
    localVariables.put(binding, expr);
  }

  protected Optional<Expr> lookupLocalVariable(LocalVariableBinding binding) {
    if (binding == null) return Optional.empty();
    return Optional.ofNullable(localVariables.get(binding));
  }

  protected Expr handleQualifiedName(QualifiedNameReference jmlQualifiedNameReference, Expr receiverExpr) {
    var result = receiverExpr;
    var qualifiedFields = jmlQualifiedNameReference.otherBindings;
    for (FieldBinding fieldBinding : qualifiedFields) {
      var fieldModel = model.getClassModel(fieldBinding.declaringClass)
              .flatMap(namedClass -> namedClass.getField(fieldBinding))
              .orElseThrow(() -> new UnsupportedJMLExpression(jmlQualifiedNameReference, "field not in named class: " + fieldBinding));

      result = fieldModel.getAccessor().apply(result);
    }

    return result;
  }

  @Override
  public String toString() {
    return "BaseExpressionParser";
  }
}
