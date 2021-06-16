package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

public class ConstantModel<S extends Sort> {

	private final String name;
	private final S sort;
	private final Expr<S> value;

	public ConstantModel(String name, S sort, Expr<S> value) {
		this.name = name;
		this.sort = sort;
		this.value = value;
	}

	public Expr<S> getValue() {
		return value;
	}
}
