package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Ref;
import de.tudarmstadt.consistency.store.ReferenceService;

import java.lang.annotation.Annotation;
import java.util.Objects;

/**
 * Created on 20.06.18.
 *
 * @author Mirko Köhler
 */
public class MapReferenceService implements ReferenceService<Object> {

	private final MapStore mapStore;

	MapReferenceService(MapStore mapStore) {
		this.mapStore = mapStore;
	}


	@Override
	public <T, R extends Ref<T, R>> R obtain(Object id, Class<? extends T> valueClass, Class<? extends Annotation> consistencyLevel) {

		//TODO: Remove these casts
		if (Objects.equals(Weak.class, consistencyLevel)) {
			return (R) new MapRef<T>(id, mapStore);
		} else if (Objects.equals(Strong.class, consistencyLevel)) {
			return (R) new MapRef<T>(id, mapStore);
		}

		throw new IllegalArgumentException("can only obtain handles with consistency level, but got " + consistencyLevel);
	}
}
