package de.tudarmstadt.consistency.store;

import static de.tudarmstadt.consistency.store.StateEvent.READ;
import static de.tudarmstadt.consistency.store.StateEvent.WRITE;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteHandle<T> implements Handle<T, StateEvent> {

	@SafeVarargs
	@Override
	public final T handle(StateEvent e, T... values) throws Exception {
		switch (e) {
			case READ:
				assert values.length == 0;
				return handleRead();

			case WRITE:
				assert values.length == 1;
				handleWrite(values[0]);
				return null;

			default:
				throw new IllegalArgumentException("cannot handle event <" + e + ">");
		}
	}

	public void set(T value) throws Exception {
		handle(WRITE, value);
	}

	public T get() throws Exception {
		return handle(READ);
	}

	protected abstract T handleRead() throws Exception;
	protected abstract void handleWrite(T value) throws Exception;
}
