package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

public class PostconditionModel {

	private final Expr oldArg;
	private final Expr newArg;
	private final Expr expr;


	public PostconditionModel(Expr oldArg, Expr newArg, Expr expr) {
		this.oldArg = oldArg;
		this.newArg = newArg;
		this.expr = expr;
	}
}
