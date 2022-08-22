package de.tuda.stg.consys.invariants.solver.subset.utils;

public abstract class AbstractZ3Function implements Z3Function {
	protected final String name;


	public AbstractZ3Function(String name) {
		this.name = name;
	}


}
