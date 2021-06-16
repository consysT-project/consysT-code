package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

public class MethodExpressionParser extends ClassExpressionParser {
	/**
	 * @param ctx
	 * @param classScope
	 * @param thisConst  Substitute all `this` references with the given const. The const needs to have
	 */
	public MethodExpressionParser(Context ctx, ClassScope classScope, Expr thisConst) {
		super(ctx, classScope, thisConst);
	}
}
