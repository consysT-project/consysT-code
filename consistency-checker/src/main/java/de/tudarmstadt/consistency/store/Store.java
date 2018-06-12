package de.tudarmstadt.consistency.store;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public interface Store<Key> {

	<T> Handle<T> obtain(Key id, Class<T> valueClass, Class<?> consistencyLevel);

}
