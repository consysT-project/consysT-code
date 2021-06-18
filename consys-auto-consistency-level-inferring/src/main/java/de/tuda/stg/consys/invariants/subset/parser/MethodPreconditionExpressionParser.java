package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;

public class MethodPreconditionExpressionParser extends MethodExpressionParser {
	/**
	 * @param ctx
	 * @param classModel
	 * @param methodModel
	 * @param thisConst   Substitute all `this` references with the given const. The const needs to have
	 */
	public MethodPreconditionExpressionParser(Context ctx, ClassModel classModel, MethodModel methodModel, Expr thisConst) {
		super(ctx, classModel, methodModel, thisConst);
	}
}
