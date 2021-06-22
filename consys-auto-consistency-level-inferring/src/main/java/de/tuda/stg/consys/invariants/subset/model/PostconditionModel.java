package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

import java.util.Optional;

public class PostconditionModel {

	protected final Expr oldConst;
	protected final Expr thisConst;
	protected final Expr resultConst;

	protected final Expr bodyExpr;


	public PostconditionModel(Expr oldConst, Expr thisConst, Optional<Expr> resultConst, Expr bodyExpr) {
		this.oldConst = oldConst;
		this.thisConst = thisConst;
		this.bodyExpr = bodyExpr.simplify();
		this.resultConst = resultConst.orElse(null);
	}

	public Expr apply(Expr oldArg, Expr thisArg, Expr resultArg) {
		if (resultArg == null) {
			return bodyExpr.substitute(
					new Expr[] {oldConst, thisConst},
					new Expr[] {oldArg, thisArg});
		} else {
			return bodyExpr.substitute(
					new Expr[] {oldConst, thisConst, resultConst},
					new Expr[] {oldArg, thisArg, resultArg});
		}
	}

	public Expr apply(Expr oldArg, Expr thisArg) {
		return apply(oldArg, thisArg, null);
	}

	public String toString() {
		return "post(" + oldConst + ", " + thisConst + ", " + resultConst + ") = " + bodyExpr;
	}
}
