package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class VoidModel extends BaseTypeModel<Sort> {

	VoidModel(ProgramModel smt) {
		super(smt);
	}

	@Override
	public boolean hasSort() {
		return false;
	}

	@Override
	public Sort toSort() {
		throw new UnsupportedOperationException("cannot get sort from void");
	}




}
