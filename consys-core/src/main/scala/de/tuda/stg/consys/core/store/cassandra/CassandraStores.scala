package de.tuda.stg.consys.core.store.cassandra

import scala.util.DynamicVariable

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
object CassandraStores {
	val currentStore : DynamicVariable[CassandraStore] = new DynamicVariable[CassandraStore](null)
	val currentTransaction : DynamicVariable[CassandraTransactionContext] = new DynamicVariable[CassandraTransactionContext](null)
}
