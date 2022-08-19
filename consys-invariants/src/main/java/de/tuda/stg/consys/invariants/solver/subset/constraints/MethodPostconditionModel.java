package de.tuda.stg.consys.invariants.solver.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.utils.Z3Function3;

public class MethodPostconditionModel implements Z3Function3 {
	private final Z3Function3 fun;
	private final Z3Function3[] bodyElements;

	MethodPostconditionModel(Z3Function3 fun, Z3Function3[] bodyElements) {
		this.fun = fun;
		this.bodyElements = bodyElements;
	}

	@Override
	public Expr apply(Expr... args) {
		return fun.apply(args);
	}

	@Override
	public Expr apply(Expr oldConst, Expr thisConst, Expr returnConst) {
		return fun.apply(oldConst, thisConst, returnConst);
	}

	public Expr[] applyWithSplitBody(Expr oldArg, Expr thisArg, Expr resultArg) {
		var result = new Expr[bodyElements.length];
		for (int i = 0; i < bodyElements.length; i++) {
			Z3Function3 pred = bodyElements[i];
			result[i] = pred.apply(oldArg, thisArg, resultArg);
		}

		return result;
	}


}
