package de.tudarmstadt.consistency.store.javaimpl;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
@FunctionalInterface
public interface Transaction<Context extends TransactionContext> {

	void executeWith(Context context) throws Exception;

}
