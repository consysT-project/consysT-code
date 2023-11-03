package de.tuda.stg.consys.invariants.solver.subset.model.types;

import com.microsoft.z3.IntSort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

public class IntModel extends BaseTypeModel<IntSort> {

	IntModel(ProgramModel model) {
		super(model);
	}

	@Override
	public IntSort toSort() {
		return model.ctx.getIntSort(); //IntSort is cached in ctx
	}


}
