package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.store.Handle;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapHandle<T> implements Handle<T> {

	private final Object id;
	private final MapStore store;


	MapHandle(Object id, MapStore store) {
		this.id = id;
		this.store = store;
	}

	@Override
	public void set(T value) {
		store.put(id, value);
	}

	@Override
	@SuppressWarnings("unchecked")
	public T get() {
		return (T) store.get(id);
	}
}
