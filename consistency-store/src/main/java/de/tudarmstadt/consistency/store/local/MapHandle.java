package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.ReadWriteHandle;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapHandle<T> extends ReadWriteHandle<T> {

	private final Object id;
	private final MapStore store;


	MapHandle(Object id, MapStore store) {
		this.id = id;
		this.store = store;
	}


	@Override
	protected T handleRead() throws Exception {
		return (T) store.get(id);
	}

	@Override
	protected void handleWrite(T value) throws Exception {
		store.put(id, value);
	}
}
