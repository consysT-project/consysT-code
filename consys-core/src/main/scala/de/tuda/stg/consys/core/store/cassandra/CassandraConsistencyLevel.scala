package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}

trait CassandraConsistencyLevel extends ConsistencyLevel[CassandraStore] {

	override def toProtocol(store : CassandraStore) : CassandraConsistencyProtocol[this.type]
}
