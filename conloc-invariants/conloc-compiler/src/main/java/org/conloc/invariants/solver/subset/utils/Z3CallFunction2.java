package org.conloc.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public class Z3CallFunction2 extends Z3CallFunction implements Z3Function2 {

	Z3CallFunction2(String name, FuncDecl func) {
		super(name, func);
		if (func.getArity() != 2)
			throw new IllegalArgumentException("function arity != 2: " + func);
	}

	public Expr apply(Expr arg1, Expr arg2) {
		return super.apply(arg1, arg2);
	}
}
