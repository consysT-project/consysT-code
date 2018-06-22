package de.tudarmstadt.consistency.store.local;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.TransactionContext;

import java.lang.annotation.Annotation;
import java.util.Objects;

/**
 * Created on 20.06.18.
 *
 * @author Mirko Köhler
 */
public class MapTransactionContext implements TransactionContext<Object> {

	private final MapStore mapStore;

	MapTransactionContext(MapStore mapStore) {
		this.mapStore = mapStore;
	}


	@Override
	public <T> MapRef<T> obtain(Object id, Class<? super T> valueClass, Class<? extends Annotation> consistencyLevel) {
		if (Objects.equals(Weak.class, consistencyLevel)) {
			return new MapRef<>(id, mapStore);
		} else if (Objects.equals(Strong.class, consistencyLevel)) {
			return new MapRef<>(id, mapStore);
		}

		throw new IllegalArgumentException("can only obtain handles with consistency level, but got " + consistencyLevel);
	}


}
