package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.ConsistencyLabel
import de.tuda.stg.consys.core.store.{Handler, StoreConsistencyLevel}

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
class CassandraHandler[T <: java.io.Serializable : TypeTag](
	val addr : String,
	val level : StoreConsistencyLevel {type StoreType = CassandraStore}
) extends Handler[CassandraStore, T] with Serializable {

	override def resolve(tx : => CassandraStore#TxContext) : CassandraStore#RawType[T] = {
		tx.lookupRaw[T](addr, level)
	}

	/* This method is for convenience use in transactions */
	def resolve() : CassandraStore#RawType[T] =
		resolve(CassandraStores.getCurrentTransaction)
}
