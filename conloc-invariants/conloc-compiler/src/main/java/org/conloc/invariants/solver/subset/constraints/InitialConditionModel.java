package org.conloc.invariants.solver.subset.constraints;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.subset.utils.Z3Function1;

public class InitialConditionModel implements Z3Function1 {
	private final Z3Function1 fun;

	InitialConditionModel(Z3Function1 fun) {
		this.fun = fun;
	}

	@Override
	public Expr apply(Expr... args) {
		return fun.apply(args);
	}

	@Override
	public Expr apply(Expr thisConst) {
		return fun.apply(thisConst);
	}
}
