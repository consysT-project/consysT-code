package de.tuda.stg.consys.experimental.lang.store.cassandra

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}
import de.tuda.stg.consys.experimental.lang.store.cassandra.CassandraTxContext.CassandraTxContextBinding
import de.tuda.stg.consys.experimental.lang.store.{CachedTxContext, ConsistencyLevel, Handler, TxContext}

import scala.reflect.runtime.universe.TypeTag
import scala.collection.mutable

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
case class CassandraTxContext(store : CassandraStore) extends TxContext with CassandraTxContextBinding with CachedTxContext {
	protected type CachedType[_] = CassandraObject[_]

	import store._


	override def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] = {
		super.replicate[T](addr, obj, level)
	}


	override def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] = {
			super.lookup[T](addr, level)
	}

	private[cassandra] def commit() : Unit = {
		store.CassandraBinding.writeObjects(cache.values.map(obj => (obj.getAddr, obj.getState)), CLevel.ONE)
	}

	override protected def refToCached[T <: ObjType : TypeTag](ref : RefType[T]) : CachedType[T] =
		ref.getObject

	override protected def cachedToRef[T <: ObjType : TypeTag](cached : CachedType[T]) : RefType[T] =
		CassandraHandler[T](cached.asInstanceOf[CassandraObject[T with Serializable]])
}

object CassandraTxContext {

	trait CassandraTxContextBinding extends TxContext {
		type StoreType = CassandraStore

		import store._
		override def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] = {
			val cassObj = new WeakCassandraObject(addr, obj)
			CassandraHandler(cassObj)
		}

		override def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] = {
			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ONE)
			val obj = new WeakCassandraObject(addr, raw)
			CassandraHandler(obj)
		}
	}
}