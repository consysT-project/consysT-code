package de.tuda.stg.consys.invariants.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Function1;

public class FieldInvariantModel implements Z3Function1 {
	private final Z3Function1 fun;

	FieldInvariantModel(Z3Function1 fun) {
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
