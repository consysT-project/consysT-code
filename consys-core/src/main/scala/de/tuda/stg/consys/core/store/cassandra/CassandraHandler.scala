package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.ConsistencyLevel
import de.tuda.stg.consys.core.store.{Handler, StoreConsistencyLevel}

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
class CassandraHandler[T <: java.io.Serializable : TypeTag](
	val addr : String,
	@transient var obj : CassandraObject[T],
	val level : StoreConsistencyLevel {type StoreType = CassandraStore}
) extends Handler[CassandraStore, T] with Serializable {

	override def resolve(tx : => CassandraStore#TxContext) : CassandraStore#RawType[T] = {
		if (obj == null) {
			//The obj may be null, e.g., if the handler has been serialized. In that case, we have
			//to look up the handled object in the store. This is done via the consistency level
			//of the handled object. TODO: Can this be just a local lookup?
			obj = level.toModel(tx.store).lookupRaw(addr)
		}
		obj
	}

	def resolve() : CassandraStore#RawType[T] =
		resolve(CassandraStores.currentTransaction.value)
}
