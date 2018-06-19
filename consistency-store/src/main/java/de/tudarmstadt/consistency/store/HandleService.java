package de.tudarmstadt.consistency.store;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
public interface HandleService<Key, Event> {

	/**
	 * Retrieves a new handle for an object with the specified key. The handle operates
	 * using the specified consistency level. How a level is exactly defined depends
	 * on the concrete implementation.
	 *
	 *  @param <T> The type of the value referenced by the key.
	 *
	 * @param id The key of the database object that is accessed.
	 * @param valueClass The class of that object.
	 * @param consistencyLevel The consistency level that is used.
	 *
	 * @return A handle that handles the access to the database object specified by the
	 * given key.
	 */
	<T> Handle<T, Event> obtain(Key id, Class<? extends T> valueClass, Class<?> consistencyLevel);
}
