package de.tudarmstadt.consistency.store.impl.local;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.Store;
import org.checkerframework.com.google.common.collect.Maps;

import java.util.Map;
import java.util.Objects;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class MapStore implements Store<Object> {

	private final Map<Object, Object> data = Maps.newHashMap();


	public <T> Handle<T> obtain(Object id, Class<T> valueClass, Class<?> consistencyLevel) {

		if (Objects.equals(Weak.class, consistencyLevel)) {
			return new MapHandle<>(id, this);
		} else if (Objects.equals(Strong.class, consistencyLevel)) {
			return new MapHandle<>(id, this);
		}

		throw new IllegalArgumentException("can only obtain handles with consistency level, but got " + consistencyLevel);
	}

	void put(Object id, Object value) {
		data.put(id, value);
	}

	Object get(Object id) {
		return data.getOrDefault(id, null);
	}
}
