package de.tuda.stg.consys.invariants;

public class OnlyUsableInConstraintsException extends RuntimeException {

	public OnlyUsableInConstraintsException() {
		super("element is only usable in constraints");
	}
}
