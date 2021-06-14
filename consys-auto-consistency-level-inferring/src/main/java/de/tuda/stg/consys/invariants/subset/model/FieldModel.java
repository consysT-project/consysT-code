package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Sort;

public class FieldModel<S extends Sort> {

	private final String name;
	private final S sort;

	public FieldModel(String name, S sort) {
		this.name = name;
		this.sort = sort;
	}

	public String getName() {
		return name;
	}

	public S getSort() {
		return sort;
	}
}
