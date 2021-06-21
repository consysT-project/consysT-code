package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

import java.util.Optional;

public class PostconditionModel {

	private final Expr oldArg;
	private final Expr newArg;
	private final Expr expr;
	private final Expr result;


	public PostconditionModel(Expr oldArg, Expr newArg, Expr expr, Optional<Expr> result) {
		this.oldArg = oldArg;
		this.newArg = newArg;
		this.expr = expr;
		this.result = result.orElse(null);
	}

	public String toString() {
		return "post(" + oldArg + ", " + newArg + ", " + result + ") = " + expr;
	}
}
