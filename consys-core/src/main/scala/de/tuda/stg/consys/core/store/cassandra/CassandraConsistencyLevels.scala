package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.StoreConsistencyLevel

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
object CassandraConsistencyLevels {
	val WEAK : StoreConsistencyLevel = Weak
	val STRONG : StoreConsistencyLevel = Strong
}
