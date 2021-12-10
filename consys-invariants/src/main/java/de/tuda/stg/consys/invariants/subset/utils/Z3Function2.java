package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Expr;

public class Z3Function2 extends Z3Function {

	public Z3Function2(String name, Expr par1, Expr par2, Expr body) {
		super(name, new Expr[] { par1, par2 }, body);
	}

	public Expr apply(Expr arg1, Expr arg2) {
		return super.apply(arg1, arg2);
	}
}
