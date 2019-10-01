package de.tuda.stg.consys.objects.japi;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public interface JRef<T> {

	<R> R getField(String fieldName);

	<R> R setField(String fieldName, R value);

	<R> R invoke(String methodName, Object... args);

	void sync();

	void syncAll();

	T ref();

	boolean isAvailable();

	void await();

	String addr();
}
