package de.tuda.stg.consys.japi;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public interface Ref<T> {

	default T ref() {
		throw new UnsupportedOperationException("Use the consys-compiler plugin to resolve calls to ref().");
	}

	<R> R getField(String fieldName);

	<R> void setField(String fieldName, R value);

	<R> R invoke(String methodName, Object... args);
}
