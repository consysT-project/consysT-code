package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.ConsistencyLevel
import de.tuda.stg.consys.core.store.cassandra.{CassandraObject, CassandraStore}
import de.tuda.stg.consys.core.store.{StoreConsistencyLevel, StoreConsistencyModel}

import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Strong extends CassandraConsistencyLevel {
	override def toModel(store : StoreType) : Model = new StrongModel(store)

	private class StrongModel(val store : CassandraStore) extends CassandraConsistencyModel {
		override def toLevel : Level = Strong

		override def writeRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			txContext.acquireLock(addr)
			new StrongCassandraObject[T](addr, obj, store, txContext)
		}

		override def readRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			txContext.acquireLock(addr)
			val obj = store.CassandraBinding.readObject[T](addr, ConsistencyLevel.ALL)
			new StrongCassandraObject[T](addr, obj, store, txContext)
		}
	}

	private class StrongCassandraObject[T <: StoreType#ObjType : ClassTag](override val addr : String, override val state : T, store : StoreType, txContext : StoreType#TxContext) extends CassandraObject[T] {
		override def consistencyLevel : CassandraStore#Level = Strong

		override protected[cassandra] def writeToStore(store : CassandraStore) : Unit =
			store.CassandraBinding.writeObject(addr, state, ConsistencyLevel.ALL, txContext.timestamp)
	}

}