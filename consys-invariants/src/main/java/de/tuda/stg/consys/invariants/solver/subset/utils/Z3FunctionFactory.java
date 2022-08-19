package de.tuda.stg.consys.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;

public interface Z3FunctionFactory<F extends Z3Function> {

	F makeFunction(String name, Expr[] parameters, Expr body);
	<F1 extends Z3Function1> F1 makeFunction1(String name, Expr par1, Expr body);
	<F2 extends Z3Function2> F2 makeFunction2(String name, Expr par1, Expr par2, Expr body);
	<F3 extends Z3Function3> F3 makeFunction3(String name, Expr par1, Expr par2, Expr par3, Expr body);
}
