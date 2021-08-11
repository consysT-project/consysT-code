package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.ProgramModel;

public class StringModel extends BaseTypeModel<Sort> {

	private Sort stringSort;

	StringModel(ProgramModel model) {
		super(model);
		stringSort = model.ctx.mkStringSort();
	}

	@Override
	public boolean hasSort() {
		return true;
	}

	@Override
	public Sort toSort() {
		return stringSort;
	}




}
