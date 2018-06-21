package de.tudarmstadt.consistency.store.impl;

import de.tudarmstadt.consistency.store.Operation;
import de.tudarmstadt.consistency.store.Ref;
import de.tudarmstadt.consistency.store.cassandra.CassandraRef;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteRef<T, R extends ReadWriteRef<T, R>> implements Ref<T, R> {

	public void write(T value) throws Exception {
		handle(eventWrite(), value);
	}

	public T read() throws Exception {
		return handle(eventRead(), null);
	}

	protected abstract T handleRead() throws Exception;
	protected abstract void handleWrite(T value) throws Exception;

//	@Override
//	public <A, B> B handle(Operation<T, R, A, B> e, A param) throws Exception {
//		return e.compute(R.this, param);
//	}

	//TODO: Is it possible to make these static?
	private Operation<T, R, Void, T> eventRead() {
		return (ref, additionalParameter) -> ref.handleRead();
	}

	private Operation<T, R, T, Void> eventWrite() {
		return (ref, additionalParameter) -> {
			ref.handleWrite(additionalParameter);
			return null;
		};
	}







}
