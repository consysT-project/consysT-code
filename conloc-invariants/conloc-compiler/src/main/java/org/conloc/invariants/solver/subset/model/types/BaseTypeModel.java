package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;

public abstract class BaseTypeModel<S extends Sort> implements TypeModel<S> {

	final ProgramModel model;

	protected BaseTypeModel(ProgramModel model) {
		this.model = model;
	}
}
