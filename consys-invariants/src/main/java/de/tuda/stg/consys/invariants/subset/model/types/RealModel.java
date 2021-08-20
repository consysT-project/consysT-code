package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.RealSort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class RealModel extends BaseTypeModel<RealSort> {

	RealModel(ProgramModel smt) {
		super(smt);
	}

	@Override
	public RealSort toSort() {
		return model.ctx.getRealSort(); //IntSort is cached in ctx
	}


}
