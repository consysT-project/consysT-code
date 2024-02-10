package de.tuda.stg.consys.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

import java.util.Arrays;

public class Z3CallFunctionFactory implements Z3FunctionFactory<Z3CallFunction> {

	public final ProgramModel model;

	public Z3CallFunctionFactory(ProgramModel model) {
		this.model = model;
	}

	private FuncDecl makeFuncDecl(String name, Expr[] parameters, Expr body)  {
		FuncDecl func = model.ctx.mkFreshFuncDecl(name, Arrays.stream(parameters).map(e -> e.getSort()).toArray(Sort[]::new), body.getSort());


		var funcDef = model.ctx.mkForall(
				parameters,
				model.ctx.mkEq(func.apply(parameters), body.simplify()),
				1,
				null,
				null,
				null,
				null
		);


		model.solver.add(funcDef);

		return func;
	}

	@Override
	public Z3CallFunction makeFunction(String name, Expr[] parameters, Expr body) {
		return new Z3CallFunction(name, makeFuncDecl(name, parameters, body));
	}

	@Override
	public Z3CallFunction1 makeFunction1(String name, Expr par1, Expr body) {
		return new Z3CallFunction1(name, makeFuncDecl(name, new Expr[] { par1 }, body));
	}

	@Override
	public Z3CallFunction2 makeFunction2(String name, Expr par1, Expr par2, Expr body) {
		return new Z3CallFunction2(name, makeFuncDecl(name, new Expr[] { par1, par2 }, body));
	}

	@Override
	public Z3CallFunction3 makeFunction3(String name, Expr par1, Expr par2, Expr par3, Expr body) {
		return new Z3CallFunction3(name, makeFuncDecl(name, new Expr[] { par1, par2, par3 }, body));
	}
}
