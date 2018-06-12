package de.tu_darmstadt.consistency_types.store;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public interface Store<Key> {

	<T> Handle<T> obtain(Key id, Class<T> valueClass, Class<?> consistencyLevel);

}
