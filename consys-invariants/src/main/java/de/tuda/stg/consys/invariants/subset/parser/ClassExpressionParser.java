package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

import java.util.Optional;
import java.util.function.Supplier;

/**
 * Parser for parsing expression inside of classes.
 */
public class ClassExpressionParser extends BaseExpressionParser {

	// The scope of the class in which this expression is parsed. Used to resolve field names.
	private final BaseClassModel classModel;
	// A const definition for substituting this references. The sort has to be the sort of the class.
	private Expr thisConst; // Can be null.

	/**
	 *
	 * @param thisConst Substitute all `this` references with the given const. The const needs to have
	 *                  the same sort as the class that is parsed.
	 */
	public ClassExpressionParser(ProgramModel smt, BaseClassModel classModel, Expr thisConst) {
		super(smt);

		if (thisConst != null && !thisConst.getSort().equals(classModel.getClassSort()))
			throw new IllegalArgumentException("the sort for `this` has to match the sort of the class");

		this.classModel = classModel;
		this.thisConst = thisConst;
	}

	@Override
	protected Expr parseExpression(Expression expression, int depth) {
		if (expression instanceof ThisReference) {
			return parseThisReference((ThisReference) expression);
		}

		if (expression instanceof JmlFieldReference) {
			return parseJmlFieldReference((JmlFieldReference) expression, depth);
		}

		return super.parseExpression(expression, depth + 1);
	}

	@Override
	protected Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
		Optional<Expr> constantExpr = classModel.getConstant(jmlSingleNameReference)
				.map(cons -> cons.getValue());

		if (constantExpr.isPresent()) {
			return constantExpr.get();
		}

		Optional<Expr> fieldExpr = classModel.getField(jmlSingleNameReference)
				.map(field -> field.getAccessor().apply(thisConst));

		if (fieldExpr.isPresent()) {
			return fieldExpr.get();
		}

		return super.parseJmlSingleReference(jmlSingleNameReference);
	}

	protected Expr parseThisReference(ThisReference thisReference) {
		return thisConst;
	}

	protected Expr parseJmlFieldReference(JmlFieldReference fieldReference, int depth) {
		Expr receiver = parseExpression(fieldReference.receiver, depth + 1);
		String fieldName = String.valueOf(fieldReference.token);

		if (fieldReference.binding.declaringClass.equals(classModel.getBinding())) {
			return classModel.getField(fieldReference)
					.map(field -> field.getAccessor().apply(receiver))
					.orElseThrow(() -> new UnsupportedJMLExpression(fieldReference));
		}

		throw new UnsupportedJMLExpression(fieldReference);
	}

	/**
	 * Visits method call like {@code getValue()} or {@code other.getValue()}.
	 *
	 * @return the result expression of the called method if it has one, {@code null} otherwise
	 */
//	@Override
//	public Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend) {
//
//
//		return handleMethodCall(thisConst, classModel, jmlMessageSend.binding, jmlMessageSend.arguments)
//				.orElseGet(() -> super.parseJmlMessageSend(jmlMessageSend));
//
////		var mbMethodModel = classModel.getMethod(jmlMessageSend.binding);
////
////		if (mbMethodModel.isEmpty()) {
////			return super.parseJmlMessageSend(jmlMessageSend);
////		}
////
////		var methodModel = mbMethodModel.get();
////
////		if (!methodModel.isZ3Usable()) {
////			throw new UnsupportedJMLExpression(jmlMessageSend);
////		}
////
////
////		final Expr[] argExprs;
////		if (jmlMessageSend.arguments == null) {
////			argExprs = new Expr[0];
////		} else {
////			argExprs = Arrays.stream(jmlMessageSend.arguments)
////					.map(this::parseExpression)
////					.toArray(Expr[]::new);
////		}
////
////		var z3Func = methodModel.getZ3FuncDecl()
////				.orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend));
////
////
////		Expr[] argExprsAndThis =  Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisConst, thisConst);
////		return model.ctx.mkApp(z3Func, argExprsAndThis);
//	}


	protected <T> T withThisReference(Expr otherConst, Supplier<T> f) {
		Expr prev = this.thisConst;
		thisConst = otherConst;

		T result = null;
		try {
			result = f.get();
		} finally {
			thisConst = prev;
		}

		return result;
	}

	protected Expr getThisConst() {
		return thisConst;
	}

	protected BaseClassModel getClassModel() {
		return classModel;
	}


}
