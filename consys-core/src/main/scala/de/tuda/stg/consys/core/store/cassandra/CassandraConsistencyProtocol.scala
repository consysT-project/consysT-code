package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}

trait CassandraConsistencyProtocol[Level <: ConsistencyLevel[CassandraStore]] extends ConsistencyProtocol[CassandraStore, Level] {

	def commit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit

}

