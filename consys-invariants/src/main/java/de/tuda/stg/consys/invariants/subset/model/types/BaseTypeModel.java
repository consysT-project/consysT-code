package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.ProgramModel;

public abstract class BaseTypeModel<S extends Sort> implements TypeModel<S> {

	final ProgramModel model;

	protected BaseTypeModel(ProgramModel model) {
		this.model = model;
	}
}
