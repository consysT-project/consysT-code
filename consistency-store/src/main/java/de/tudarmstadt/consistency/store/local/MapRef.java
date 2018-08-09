package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.store.impl.ReadWriteRef;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapRef<T> extends ReadWriteRef<T> {

	private final Object id;
	private final MapStore store;


	MapRef(Object id, MapStore store) {
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
