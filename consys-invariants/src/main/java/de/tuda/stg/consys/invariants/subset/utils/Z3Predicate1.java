package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Expr;

public class Z3Predicate1 extends Z3Predicate {

	public Z3Predicate1(String name, Expr par1, Expr body) {
		super(name, new Expr[] { par1 }, body);
	}

	public Expr apply(Expr arg1) {
		return super.apply(arg1);
	}
}
