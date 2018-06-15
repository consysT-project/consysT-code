package de.tudarmstadt.consistency.store;

/**
 * A handle corresponds to a single database object. It can be used to read the specified object or to write
 * a new value as that object.
 *
 * @author Mirko Köhler
 */
public interface Handle<T> {

	/**
	 * Sets a new value for the database object referenced by this handle.
	 *
	 * @param value The new value.
	 *
	 * @throws Exception This method may throw an exception in case anything
	 * goes wrong (e.g. communicating with the database).
	 */
	void set(T value) throws Exception;

	/**
	 * Retrieves the value of the database object referenced by this handle.
	 *
	 * @return The value referenced by this handle.
	 *
	 * @throws Exception This method may throw an exception in case anything
	 * goes wrong (e.g. communicating with the database).
	 */
	T get() throws Exception;
}
