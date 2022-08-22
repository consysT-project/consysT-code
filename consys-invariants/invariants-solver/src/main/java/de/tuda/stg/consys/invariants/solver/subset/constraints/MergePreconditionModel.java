package de.tuda.stg.consys.invariants.solver.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.utils.Z3Function2;

public class MergePreconditionModel implements Z3Function2 {
	private final Z3Function2 fun;

	MergePreconditionModel(Z3Function2 fun) {
		this.fun = fun;
	}

	@Override
	public Expr apply(Expr... args) {
		return fun.apply(args);
	}

	@Override
	public Expr apply(Expr thisConst, Expr otherConst) {
		return fun.apply(thisConst, otherConst);
	}
}
