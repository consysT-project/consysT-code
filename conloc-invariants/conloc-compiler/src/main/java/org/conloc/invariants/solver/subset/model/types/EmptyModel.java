package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;

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
