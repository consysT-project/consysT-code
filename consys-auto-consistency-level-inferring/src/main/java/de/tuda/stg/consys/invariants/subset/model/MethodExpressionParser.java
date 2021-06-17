package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Maps;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import java.util.Map;

/**
 * Parser for parsing expression inside of methods.
 */
public class MethodExpressionParser extends ClassExpressionParser {

	private final MethodModel methodModel;


	/**
	 * @param ctx
	 * @param classScope
	 * @param thisConst  Substitute all `this` references with the given const. The const needs to have
	 */
	public MethodExpressionParser(Context ctx, ClassScope classScope, MethodModel methodModel, Expr thisConst) {
		super(ctx, classScope, thisConst);
		this.methodModel = methodModel;
	}




}
