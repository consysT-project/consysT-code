package de.tuda.stg.consys.annotations.invariants;

public class OnlyUsableInConstraintsException extends RuntimeException {

	public OnlyUsableInConstraintsException() {
		super("element is only usable in constraints");
	}
}
