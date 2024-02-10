package de.tuda.stg.consys.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public class Z3CallFunction1 extends Z3CallFunction implements Z3Function1 {

	Z3CallFunction1(String name, FuncDecl func) {
		super(name, func);
		if (func.getArity() != 1)
			throw new IllegalArgumentException("function arity != 1: " + func);
	}

	public Expr apply(Expr arg1) {
		return super.apply(arg1);
	}
}
