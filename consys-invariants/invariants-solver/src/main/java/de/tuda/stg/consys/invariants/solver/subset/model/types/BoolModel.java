package de.tuda.stg.consys.invariants.solver.subset.model.types;

import com.microsoft.z3.BoolSort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

public class BoolModel extends BaseTypeModel<BoolSort> {

	BoolModel(ProgramModel model) {
		super(model);
	}

	@Override
	public BoolSort toSort() {
		return model.ctx.getBoolSort(); //IntSort is cached in ctx
	}
}
