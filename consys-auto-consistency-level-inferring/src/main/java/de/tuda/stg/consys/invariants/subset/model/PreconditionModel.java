package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

public class PreconditionModel {

	private final Expr arg;
	private final Expr expr;


	public PreconditionModel(Expr arg, Expr expr) {
		this.arg = arg;
		this.expr = expr;
	}
}
