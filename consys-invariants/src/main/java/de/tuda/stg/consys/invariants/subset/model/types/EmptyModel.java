package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class EmptyModel extends BaseTypeModel<Sort> {

	private final String err;

	EmptyModel(ProgramModel smt, String err) {
		super(smt);
		this.err = err;
		System.err.println("Empty model created. Reason: " + err);
	}

	@Override
	public boolean hasSort() {
		return false;
	}

	@Override
	public Sort toSort() {
		throw new UnsupportedOperationException("cannot get sort from empty: " + err);
	}




}
