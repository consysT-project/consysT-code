package de.tuda.stg.consys.experimental.lang.store.cassandra

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}
import de.tuda.stg.consys.experimental.lang.store.cassandra.CassandraTxContext.CassandraTxContextBinding
import de.tuda.stg.consys.experimental.lang.store.{CachedTxContext, CommitableTxContext, TxContext}

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
case class CassandraTxContext(store : CassandraStore) extends TxContext
	with CassandraTxContextBinding
	with CommitableTxContext
	with CachedTxContext {

	protected final type CachedType[T <: java.io.Serializable] = CassandraObject[T]
	import store._

	override def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] = {
		super.replicate[T](addr, obj, level)
	}

	override def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] = {
			super.lookup[T](addr, level)
	}

	def commit() : Unit = {
		store.CassandraBinding.writeObjects(cache.values.map(obj => obj.commit()), CLevel.ONE)
	}

	override protected def refToCached[T <: ObjType : TypeTag](ref : RefType[T]) : CachedType[T] =
		ref.getObject

	override protected def cachedToRef[T <: ObjType : TypeTag](cached : CachedType[T]) : RefType[T] =
		CassandraHandler[T](cached)
}

object CassandraTxContext {

	trait CassandraTxContextBinding extends TxContext {
		type StoreType = CassandraStore
	}
}