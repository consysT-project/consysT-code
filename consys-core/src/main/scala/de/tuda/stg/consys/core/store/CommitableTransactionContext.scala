package de.tuda.stg.consys.core.store

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CommitableTransactionContext extends TransactionContext {
	private[store] def commit() : Unit
}
