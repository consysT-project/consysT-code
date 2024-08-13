package de.tuda.stg.consys.core.store.cassandra

import scala.util.DynamicVariable

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
object CassandraStores {
	private[cassandra] val currentTransaction : DynamicVariable[CassandraStore#TxContext] = new DynamicVariable[CassandraStore#TxContext](null)

	def getCurrentTransaction : Option[CassandraStore#TxContext] = {
		Option(currentTransaction.value)
	}
}
