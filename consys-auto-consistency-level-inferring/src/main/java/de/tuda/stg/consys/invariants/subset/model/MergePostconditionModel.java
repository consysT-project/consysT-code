package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

public class MergePostconditionModel {

	private final Expr oldConst;
	private final Expr otherConst;
	private final Expr thisConst;

	private final Expr bodyExpr;

	public MergePostconditionModel(Expr oldConst, Expr otherConst, Expr thisConst, Expr bodyExpr) {
		this.oldConst = oldConst;
		this.thisConst = thisConst;
		this.otherConst = otherConst;
		this.bodyExpr = bodyExpr.simplify();
	}

	public Expr apply(Expr oldArg, Expr otherArg, Expr thisArg) {
		return bodyExpr.substitute(
				new Expr[] {oldConst, thisConst, otherConst},
				new Expr[] {oldArg, thisArg, otherArg});
	}



	@Override
	public String toString() {
		return "post_merge(" + oldConst + ", " + thisConst + ", " + otherConst + ") = " + bodyExpr;
	}

}
