package de.tudarmstadt.consistency.store;

/**
 * A handle corresponds to a single database object. It can be used to read the specified object or to write
 * a new value as that object.
 *
 * @author Mirko Köhler
 */
public interface Ref<T, R extends Ref<T, R>> {

	/*
		TODO: handle probably can return and take some different types than referenced by Ref.
		A ref is a reference to one database object of type T. the handle method allows interaction
		with that object. Currently this operation is more less restricted to writes and reads.
	 */
	/**
	 * Handles an event for the database object represented by this handle.
	 * Examples for events are reading from the database or writing to the database.
	 * The concrete allowed events are defined by the database.
	 *
	 * @param e The event to handle.
	 * @param values Arguments to the event.
	 * @return A value that is produced by the event, or null if the event does not
	 * produce any value.
	 *
	 * @throws Exception if the event can not be handled, or communication with
	 * the database goes wrong.
	 */
	<X, Y> Y handle(Operation<T, R, X, Y> e, X param) throws Exception;

}
