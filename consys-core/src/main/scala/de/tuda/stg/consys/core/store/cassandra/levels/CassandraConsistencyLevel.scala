package de.tuda.stg.consys.core.store.cassandra.levels

import de.tuda.stg.consys.core.store.StoreConsistencyLevel
import de.tuda.stg.consys.core.store.cassandra.CassandraStore

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait CassandraConsistencyLevel extends StoreConsistencyLevel {
	override type StoreType = CassandraStore
	override type Model = CassandraConsistencyModel


}
