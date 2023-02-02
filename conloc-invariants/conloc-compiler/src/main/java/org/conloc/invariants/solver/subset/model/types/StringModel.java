package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;

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
