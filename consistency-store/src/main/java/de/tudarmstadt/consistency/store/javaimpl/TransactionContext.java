package de.tudarmstadt.consistency.store.javaimpl;

import java.lang.annotation.Annotation;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
public interface TransactionContext<Key> {

	//TODO: How can we force that T is annotated with the consistencyLevel
	//TODO: let obtain return a special kind of Ref and not the general ref
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
	<T> Ref<T, ?> obtain(Key id, Class<? super T> valueClass, Class<? extends Annotation> consistencyLevel);
}
