package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class RefModel extends BaseTypeModel<Sort> {

	private Sort refSort;

	RefModel(ProgramModel model, String sortName) {
		super(model);
		refSort = model.ctx.mkUninterpretedSort(sortName);
	}

	@Override
	public boolean hasSort() {
		return true;
	}

	@Override
	public Sort toSort() {
		return refSort;
	}




}
