package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.jmlspecs.jml4.ast.JmlOldExpression;
import org.jmlspecs.jml4.ast.JmlResultReference;

import java.util.Optional;

public class MethodPostconditionExpressionParser extends MethodExpressionParser {


	private Expr cachedThisConst;
	private Expr cachedOldConst;
	private Expr resultConst; // Can be null.

	/**
	 * @param ctx
	 * @param classModel
	 * @param methodModel
	 * @param thisConst   Substitute all `this` references with the given const. The const needs to have
	 */
	public MethodPostconditionExpressionParser(Context ctx, ClassModel classModel, MethodModel methodModel, Expr thisConst, Expr oldConst, Optional<Expr> resultConst) {
		super(ctx, classModel, methodModel, thisConst);

		this.cachedThisConst = thisConst;
		this.cachedOldConst = oldConst;
		this.resultConst = resultConst.orElse(null);
	}

	@Override
	public Expr parseExpression(Expression expression) {
		// "\old(...)"
		if (expression instanceof JmlOldExpression) {
			return visitOldExpression((JmlOldExpression) expression);
		}

		// \result is the result reference
    	if (expression instanceof JmlResultReference) {
    		return parseJmlResultReference((JmlResultReference) expression);
		}

		return super.parseExpression(expression);
	}



	public Expr visitOldExpression(JmlOldExpression jmlOldExpression) {
		// Change the resolution of `this` to the const for old.
		thisConst = cachedOldConst;
		Expr result = parseExpression(jmlOldExpression.expression);
		// Reset the resolution of `this`
		thisConst = cachedThisConst;

		return result;
	}

	public Expr parseJmlResultReference(JmlResultReference jmlResultReference) {
		if (resultConst == null)
			throw new IllegalArgumentException("\\result can not be used when method does return void.");

		return resultConst;
	}
}
