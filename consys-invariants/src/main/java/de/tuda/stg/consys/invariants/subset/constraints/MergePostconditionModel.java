package de.tuda.stg.consys.invariants.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Function3;

public class MergePostconditionModel implements Z3Function3 {
	private final Z3Function3 fun;

	MergePostconditionModel(Z3Function3 fun) {
		this.fun = fun;
	}

	@Override
	public Expr apply(Expr... args) {
		return fun.apply(args);
	}

	@Override
	public Expr apply(Expr oldConst, Expr otherConst, Expr thisConst) {
		return fun.apply(oldConst, otherConst, thisConst);
	}
}
