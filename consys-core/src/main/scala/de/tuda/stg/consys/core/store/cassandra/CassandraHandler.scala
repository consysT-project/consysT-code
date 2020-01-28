package de.tuda.stg.consys.core.store.cassandra

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
	def resolve() : CassandraStore#RawType[T] = CassandraStores.getCurrentTransaction match {
		case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
		case Some(tx) => resolve(tx)
	}

}
