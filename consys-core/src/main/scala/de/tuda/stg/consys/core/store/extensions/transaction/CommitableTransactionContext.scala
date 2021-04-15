package de.tuda.stg.consys.core.store.extensions.transaction

import de.tuda.stg.consys.core.store.{Store, TransactionContext}

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CommitableTransactionContext[StoreType <: Store] extends TransactionContext[StoreType] {
	private[store] def commit() : Unit
}
