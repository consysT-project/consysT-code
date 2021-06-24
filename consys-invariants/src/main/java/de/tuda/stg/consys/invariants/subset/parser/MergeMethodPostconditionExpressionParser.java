package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.MergeMethodModel;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.jmlspecs.jml4.ast.JmlQualifiedNameReference;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

import java.util.Optional;

public class MergeMethodPostconditionExpressionParser extends MethodPostconditionExpressionParser {

	private final Expr otherConst;

	/**
	 * @param ctx
	 * @param classModel
	 * @param methodModel
	 * @param thisConst   Substitute all `this` references with the given const. The const needs to have
	 */
	public MergeMethodPostconditionExpressionParser(Context ctx, ClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr oldConst, Expr otherConst) {
		super(ctx, classModel, methodModel, thisConst, oldConst, null);
		this.otherConst = otherConst;
	}

	@Override
	public Expr parseExpression(Expression expression) {
		if (expression instanceof JmlQualifiedNameReference) {
			return parseJmlQualifiedNameReference((JmlQualifiedNameReference) expression);
		}

		return super.parseExpression(expression);
	}

	public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
		Argument mergeArg = getMergeMethod().getArgument();

		if (jmlSingleNameReference.binding.equals(mergeArg.binding)) {
			return otherConst;
		}

		return super.parseJmlSingleReference(jmlSingleNameReference);
	}

	public Expr parseJmlQualifiedNameReference(JmlQualifiedNameReference jmlQualifiedNameReference) {
		Argument mergeArg = getMergeMethod().getArgument();

		if (jmlQualifiedNameReference.binding.equals(mergeArg.binding)) {
			FieldBinding fieldBinding = jmlQualifiedNameReference.otherBindings[0];

			return getClassModel().getField(fieldBinding)
					.map(field -> field.getAccessor().apply(otherConst))
					.orElseThrow(() -> new WrongJMLArgumentsExpression(jmlQualifiedNameReference));
		}

		throw new UnsupportedJMLExpression(jmlQualifiedNameReference);
	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}


}
