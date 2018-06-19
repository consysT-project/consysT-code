package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.*;
import org.checkerframework.com.google.common.collect.Maps;

import java.util.Map;
import java.util.Objects;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapStore implements Store<Object, StateEvent, MapStore.MapHandleService> {

	private final Map<Object, Object> data = Maps.newHashMap();

	@Override
	public void commit(Transaction<MapHandleService> actions, Class<?> isolationLevel) throws Exception {
		actions.executeWith(new MapHandleService());
	}


	class MapHandleService implements HandleService<Object, StateEvent> {

		@Override
		public <T> Handle<T, StateEvent> obtain(Object id, Class<? extends T> valueClass, Class<?> consistencyLevel) {

			if (Objects.equals(Weak.class, consistencyLevel)) {
				return new MapHandle<>(id, MapStore.this);
			} else if (Objects.equals(Strong.class, consistencyLevel)) {
				return new MapHandle<>(id, MapStore.this);
			}

			throw new IllegalArgumentException("can only obtain handles with consistency level, but got " + consistencyLevel);
		}
	}

	void put(Object id, Object value) {
		data.put(id, value);
	}

	Object get(Object id) {
		return data.getOrDefault(id, null);
	}
}
