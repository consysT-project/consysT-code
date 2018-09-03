package de.tudarmstadt.consistency.store.javaimpl.impl;


import de.tudarmstadt.consistency.store.javaimpl.Ref;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public interface IReadWriteRef<T, R extends IReadWriteRef<T, R>> extends Ref<T, R> {

	void write(T value) throws Exception;

	T read() throws Exception;



}
