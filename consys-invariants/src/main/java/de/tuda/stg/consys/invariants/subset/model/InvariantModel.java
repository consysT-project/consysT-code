package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;

/**
 * Defines invariants {@code I(arg) = expr}.
 */
public class InvariantModel {

	private final Expr arg;
	private final Expr expr;

	public InvariantModel(Expr arg, Expr expr) {
		this.arg = arg;
		this.expr = expr.simplify();
	}

	public Expr apply(Expr parameter) {
//		if (parameter.getSort() != arg.getSort()) {
//			throw new IllegalArgumentException("parameter " + parameter + " does not have the correct sort. was: " + parameter.getSort() + ", required: " + arg.getSort());
//		}

		return expr.substitute(arg, parameter);
	}

	@Override
	public String toString() {
		return "I(" + arg + ") = " + expr;
	}
}
