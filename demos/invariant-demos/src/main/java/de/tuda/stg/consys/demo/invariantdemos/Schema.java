package de.tuda.stg.consys.demo.invariantdemos;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.util.Random;

public abstract class Schema<T> {

	public abstract T newInstance();
	public abstract Class<T> instanceClass();

	public abstract void doOperation(JRef<T> ref);





	private void randomTransaction() {

	}

	private void transaction1() {

	}

	private void transaction2() {

	}

	private void transaction3() {

	}
}
