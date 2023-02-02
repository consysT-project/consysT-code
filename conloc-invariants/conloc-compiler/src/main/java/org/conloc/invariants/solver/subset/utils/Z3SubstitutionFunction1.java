package org.conloc.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;

public class Z3SubstitutionFunction1 extends Z3SubstitutionFunction implements Z3Function1 {

	public Z3SubstitutionFunction1(String name, Expr par1, Expr body) {
		super(name, new Expr[] { par1 }, body);
	}

	public Expr apply(Expr arg1) {
		return super.apply(arg1);
	}
}
