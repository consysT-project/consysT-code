package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.store.Operation;
import de.tudarmstadt.consistency.store.impl.ReadWriteRef;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapRef<T> extends ReadWriteRef<T, MapRef<T>> {

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

	@Override
	public <X, Y> Y handle(Operation<T, MapRef<T>, X, Y> e, X param) throws Exception {
		return e.compute(this, param);
	}
}
