package de.tu_darmstadt.consistency_types.store;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public interface Store {

	<T> Handle<T> obtain(Object id, Class<?> consistencyLevel);

}
