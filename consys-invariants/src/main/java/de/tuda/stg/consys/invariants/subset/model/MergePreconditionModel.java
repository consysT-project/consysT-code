package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

public class MergePreconditionModel {

	private final Expr thisConst;
	private final Expr otherConst;
	private final Expr bodyExpr;


	public MergePreconditionModel(Expr thisConst, Expr otherConst, Expr bodyExpr) {
		this.thisConst = thisConst;
		this.otherConst = otherConst;
		this.bodyExpr = bodyExpr.simplify();
	}

	public Expr apply(Expr thisArg, Expr otherArg) {
		return bodyExpr.substitute(
				new Expr[] {thisConst, otherConst},
				new Expr[] {thisArg, otherArg});
	}

	@Override
	public String toString() {
		return "pre_merge(" + thisConst + ", " + otherConst + ") = " + bodyExpr;
	}

}
