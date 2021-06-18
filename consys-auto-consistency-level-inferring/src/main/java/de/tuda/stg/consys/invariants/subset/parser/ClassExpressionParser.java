package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.ConstantModel;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;
import org.jmlspecs.jml4.ast.JmlMessageSend;

import org.jmlspecs.jml4.ast.JmlSingleNameReference;

import java.util.Optional;

/**
 * Parser for parsing expression inside of classes.
 */
public class ClassExpressionParser extends BaseExpressionParser {

	// The scope of the class in which this expression is parsed. Used to resolve field names.
	private final ClassModel classModel;
	// A const definition for substituting this references. The sort has to be the sort of the class.
	private final Expr thisConst;

	/**
	 *
	 * @param ctx
	 * @param classModel
	 * @param thisConst Substitute all `this` references with the given const. The const needs to have
	 *                  the same sort as the class that is parsed.
	 */
	public ClassExpressionParser(Context ctx, ClassModel classModel, Expr thisConst) {
		super(ctx);

		if (!thisConst.getSort().equals(classModel.getClassSort()))
			throw new IllegalArgumentException("the sort for `this` has to match the sort of the class");

		this.classModel = classModel;
		this.thisConst = thisConst;
	}

	@Override
	public Expr parseExpression(Expression expression) {
		if (expression instanceof ThisReference) {
			return parseThisReference((ThisReference) expression);
		}

		if (expression instanceof JmlFieldReference) {
			return parseJmlFieldReference((JmlFieldReference) expression);
		}

		return super.parseExpression(expression);
	}

	@Override
	public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
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

	public Expr parseThisReference(ThisReference thisReference) {
		return thisConst;
	}

	public Expr parseJmlFieldReference(JmlFieldReference fieldReference) {
		Expr receiver = parseExpression(fieldReference.receiver);
		String fieldName = String.valueOf(fieldReference.token);

		if (receiver.getSort().equals(classModel.getClassSort())) {
			return classModel.getField(fieldReference)
					.map(field -> field.getAccessor().apply(receiver))
					.orElseThrow(() -> new WrongJMLArgumentsExpression(fieldReference));
		} else if (receiver.getSort() instanceof ArraySort) {
			if ("length".equals(fieldName)) {
				//TODO: How to handle array lengths?
				throw new UnsupportedJMLExpression(fieldReference);
			}
		}

		throw new UnsupportedJMLExpression(fieldReference);
	}

	/**
	 * Visits method call like {@code getValue()} or {@code other.getValue()}.
	 *
	 * @return the result expression of the called method if it has one, {@code null} otherwise
	 */
	public Expr visitJmlMessageSend(JmlMessageSend jmlMessageSend) {



//		Expr methodReturnValue = scope.getReturnValue(String.valueOf(jmlMessageSend.selector));
//
//		if (methodReturnValue != null) {
//			// now distinguish between this and other -> check if its a this reference
//			if (jmlMessageSend.receiver instanceof ThisReference) {
//				return methodReturnValue;
//			} else {
//				// only method calls within the same class supported
//				int varSize = scope.getClassVariables().size();
//				Expr[] newVars = new Expr[varSize];
//				Expr[] otherVars = new Expr[varSize];
//				newVars =
//						scope.getClassVariables().values().stream()
//								.map(InternalVar::getNewValue)
//								.collect(Collectors.toList())
//								.toArray(newVars);
//				otherVars =
//						scope.getClassVariables().values().stream()
//								.map(InternalVar::getOtherValue)
//								.collect(Collectors.toList())
//								.toArray(otherVars);
//				return methodReturnValue.substitute(newVars, otherVars);
//			}
//		}

		throw new WrongJMLArgumentsExpression(jmlMessageSend);
	}


}
