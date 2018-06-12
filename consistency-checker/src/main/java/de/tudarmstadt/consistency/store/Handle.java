package de.tudarmstadt.consistency.store;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public interface Handle<T> {

	void set(T value) throws Exception;

	T get() throws Exception;
}
