package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Expr;

public abstract class AbstractZ3Function implements Z3Function {
	protected final String name;


	public AbstractZ3Function(String name) {
		this.name = name;
	}


}
