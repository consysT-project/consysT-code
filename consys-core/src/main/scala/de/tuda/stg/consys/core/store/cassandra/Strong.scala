package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.ConsistencyLevel
import de.tuda.stg.consys.core.store.{StoreConsistencyLevel, StoreConsistencyModel}

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Strong extends StoreConsistencyLevel {
	override type StoreType = CassandraStore
	override def toModel(store : StoreType) : StoreConsistencyModel {type StoreType = Strong.this.StoreType} = new Model(store)

	private class Model(val store : CassandraStore) extends StoreConsistencyModel {
		override type StoreType = CassandraStore

		override def toLevel : StoreConsistencyLevel = Strong

		override def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			txContext.acquireLock(addr)
			new StrongCassandraObject(addr, obj, store, txContext)
		}

		override def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			txContext.acquireLock(addr)
			val obj = store.CassandraBinding.readObject[T](addr, ConsistencyLevel.ALL)
			new StrongCassandraObject(addr, obj, store, txContext)
		}
	}

	private class StrongCassandraObject[T <: java.io.Serializable : ClassTag](override val addr : String, override val state : T, store : StoreType, txContext : StoreType#TxContext) extends CassandraObject[T] {
		override def consistencyLevel : StoreConsistencyLevel { type StoreType = CassandraStore } = Strong

		override protected[cassandra] def writeToStore(store : CassandraStore) : Unit =
			store.CassandraBinding.writeObject(addr, state, ConsistencyLevel.ALL, txContext.timestamp)
	}

}