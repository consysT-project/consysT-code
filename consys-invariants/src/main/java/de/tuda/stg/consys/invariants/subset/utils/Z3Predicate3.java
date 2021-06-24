package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Expr;

public class Z3Predicate3 extends Z3Predicate {

	public Z3Predicate3(String name, Expr par1, Expr par2, Expr par3, Expr body) {
		super(name, new Expr[] { par1, par2, par3 }, body);
	}

	public Expr apply(Expr arg1, Expr arg2, Expr arg3) {
		return super.apply(arg1, arg2, arg3);
	}
}
