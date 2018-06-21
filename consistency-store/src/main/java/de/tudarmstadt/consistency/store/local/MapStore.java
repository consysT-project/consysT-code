package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.store.Store;
import de.tudarmstadt.consistency.store.Transaction;
import org.checkerframework.com.google.common.collect.Maps;

import java.util.Map;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapStore implements Store<Object, MapReferenceService> {

	private final Map<Object, Object> data;

	private MapStore() {
		data = Maps.newHashMap();
	}

	public static MapStore create() {
		return new MapStore();
	}

	@Override
	public void commit(Transaction<MapReferenceService> actions, Class<?> isolationLevel) throws Exception {
		actions.executeWith(new MapReferenceService(this));
	}

	void put(Object id, Object value) {
		data.put(id, value);
	}

	Object get(Object id) {
		return data.getOrDefault(id, null);
	}


}
