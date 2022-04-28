package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Expr;

public class Z3SubstitutionFunctionFactory implements Z3FunctionFactory<Z3SubstitutionFunction> {


	@Override
	public Z3SubstitutionFunction makeFunction(String name, Expr[] parameters, Expr body) {
		return new Z3SubstitutionFunction(name, parameters, body);
	}

	@Override
	public Z3SubstitutionFunction1 makeFunction1(String name, Expr par1, Expr body) {
		return new Z3SubstitutionFunction1(name, par1, body);
	}

	@Override
	public Z3SubstitutionFunction2 makeFunction2(String name, Expr par1, Expr par2, Expr body) {
		return new Z3SubstitutionFunction2(name, par1, par2, body);
	}

	@Override
	public Z3SubstitutionFunction3 makeFunction3(String name, Expr par1, Expr par2, Expr par3, Expr body) {
		return new Z3SubstitutionFunction3(name, par1, par2, par3, body);
	}
}
