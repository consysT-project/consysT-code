package de.tudarmstadt.consistency.store.impl;

import de.tudarmstadt.consistency.store.Operation;
import de.tudarmstadt.consistency.store.Ref;
import de.tudarmstadt.consistency.store.cassandra.CassandraRef;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteRef<T> implements IReadWriteRef<T, ReadWriteRef<T>> {

	public void write(T value) throws Exception {
		handle(eventWrite(), value);
	}

	public T read() throws Exception {
		return handle(eventRead(), null);
	}

	protected abstract T handleRead() throws Exception;
	protected abstract void handleWrite(T value) throws Exception;

	@Override
	public <A, B> B handle(Operation<T, ReadWriteRef<T>, A, B> e, A param) throws Exception {
		return e.compute(this, param);
	}

	//TODO: Is it possible to make these static?
	private Operation<T, ReadWriteRef<T>, Void, T> eventRead() {
		return (ref, additionalParameter) -> ref.handleRead();
	}

	private Operation<T, ReadWriteRef<T>, T, Void> eventWrite() {
		return (ref, additionalParameter) -> {
			ref.handleWrite(additionalParameter);
			return null;
		};
	}







}
