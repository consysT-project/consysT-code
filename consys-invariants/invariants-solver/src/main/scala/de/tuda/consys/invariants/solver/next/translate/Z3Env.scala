package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{Context, Params, Solver}

class Z3Env(val ctx : Context = new Context()) {

	val solver : Solver = ctx.mkSolver()

	{
		val params : Params = ctx.mkParams
		params.add("enable_pre_simplify", true)
		solver.setParameters(params)
	}

}
