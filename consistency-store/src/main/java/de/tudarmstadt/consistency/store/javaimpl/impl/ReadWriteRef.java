package de.tudarmstadt.consistency.store.javaimpl.impl;


import de.tudarmstadt.consistency.store.javaimpl.Operation;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteRef<T> implements IReadWriteRef<T, ReadWriteRef<T>> {

	public void write(T value) throws Exception {
		handle(writeOp(), value);
	}

	public T read() throws Exception {
		return handle(readOp(), null);
	}

	protected abstract T handleRead() throws Exception;
	protected abstract void handleWrite(T value) throws Exception;

	@Override
	public <A, B> B handle(Operation<T, ReadWriteRef<T>, A, B> e, A param) throws Exception {
		return e.compute(this, param);
	}

	private static <T> Operation<T, ReadWriteRef<T>, Void, T> readOp() {
		return (ref, additionalParameter) -> ref.handleRead();
	}

	private static <T> Operation<T, ReadWriteRef<T>, T, Void> writeOp() {
		return (ref, additionalParameter) -> {
			ref.handleWrite(additionalParameter);
			return null;
		};
	}







}
