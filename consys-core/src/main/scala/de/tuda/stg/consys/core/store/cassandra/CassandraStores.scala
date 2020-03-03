package de.tuda.stg.consys.core.store.cassandra

import scala.util.DynamicVariable

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
object CassandraStores {
	private[cassandra] val currentStore : DynamicVariable[CassandraStore] = new DynamicVariable[CassandraStore](null)

	private[cassandra] val currentTransaction : DynamicVariable[CassandraTransactionContext] = new DynamicVariable[CassandraTransactionContext](null)


	def getCurrentStore : Option[CassandraStore] = {
		Option(currentStore.value)
	}

	private[cassandra] def setCurrentStore(store : CassandraStore) : Unit =
		if (currentStore.value == null) {
			currentStore.value = store
		} else {
			throw new IllegalStateException(s"unable to set current store. store already active.\nactive store: ${currentStore.value}\nnew store: $store")
		}


	def getCurrentTransaction : Option[CassandraTransactionContext] = {
		Option(currentTransaction.value)
	}

	private[cassandra] def setCurrentTransaction(tx : CassandraTransactionContext) : Unit =
		if (currentTransaction.value == null) {
			currentTransaction.value = tx
		} else {
			throw new IllegalStateException(s"unable to set current transaction. transaction already active.\nactive transaction: ${currentTransaction.value}\nnew transaction: $tx")
		}


}
