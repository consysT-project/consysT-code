package de.tudarmstadt.consistency.store;

/**
 * Models any kind of store. Values that are indexed by a key. They can be accessed by creating handles
 * that make it posssible to access a single database object. Handles are retrieved by specifying that key and a
 * consistency level.
 *
 *
 * @author Mirko Köhler
 */
public interface Store<Key, Context extends TransactionContext<Key>> {

	void commit(Transaction<Context> actions, Class<?> isolationLevel) throws Exception;


}
