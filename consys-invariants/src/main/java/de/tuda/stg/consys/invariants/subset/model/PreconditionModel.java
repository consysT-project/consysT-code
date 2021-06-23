package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

public class PreconditionModel {

	protected final Expr thisConst;
	protected final Expr bodyExpr;

	public PreconditionModel(Expr thisConst, Expr bodyExpr) {
		this.thisConst = thisConst;
		this.bodyExpr = bodyExpr.simplify();
	}

	public Expr apply(Expr thisArg) {
		return bodyExpr.substitute(thisConst, thisArg);
	}

	@Override
	public String toString() {
		return "pre(" + thisConst + ") = " + bodyExpr;
	}
}
