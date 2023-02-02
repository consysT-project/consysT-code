package org.conloc.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public class Z3CallFunction3 extends Z3CallFunction implements Z3Function3 {

	Z3CallFunction3(String name, FuncDecl func) {
		super(name, func);
		if (func.getArity() != 3)
			throw new IllegalArgumentException("function arity != 3: " + func);
	}

	public Expr apply(Expr arg1, Expr arg2, Expr arg3) {
		return super.apply(arg1, arg2, arg3);
	}
}
