package de.tuda.stg.consys.core.store.cassandra

import scala.util.DynamicVariable

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
object CassandraStores {
	private val currentStore : DynamicVariable[CassandraStore] = new DynamicVariable[CassandraStore](null)


	private[cassandra] val currentTransaction : DynamicVariable[CassandraTransactionContext] = new DynamicVariable[CassandraTransactionContext](null)

	def getCurrentTransaction : CassandraTransactionContext =
		currentTransaction.value

	def setCurrentTransaction(tx : CassandraTransactionContext) : Unit = currentTransaction synchronized {
		if (currentTransaction.value == null) {
			currentTransaction.value = tx
		} else {
			throw new IllegalStateException(s"unable to set current transaction. transaction already active.\nactive transaction: ${currentTransaction.value}\nnew transaction: $tx")
		}
	}

}
