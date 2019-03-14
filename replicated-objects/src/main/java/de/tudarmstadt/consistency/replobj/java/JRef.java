package de.tudarmstadt.consistency.replobj.java;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public interface JRef<T> {

	<R> R getField(String fieldName);

	<R> void setField(String fieldName, R value);

	<R> R invoke(String methodName, Object... args);

	void sync();

	T remote();
}
