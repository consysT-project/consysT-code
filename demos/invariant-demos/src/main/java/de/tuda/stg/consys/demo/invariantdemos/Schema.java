package de.tuda.stg.consys.demo.invariantdemos;

import de.tuda.stg.consys.core.legacy.CanBeMerged;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.util.Random;

public abstract class Schema<T extends CanBeMerged<T>> {

	public abstract T newInstance();
	public abstract Class<T> instanceClass();

	public abstract void doOperation(JRef<T> ref);


}
