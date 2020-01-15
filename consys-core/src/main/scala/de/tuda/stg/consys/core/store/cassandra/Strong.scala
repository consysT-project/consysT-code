package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}
import de.tuda.stg.consys.core.ConsistencyLevel
import de.tuda.stg.consys.core.store.{StoreConsistencyModel, StoreConsistencyLevel}
import de.tuda.stg.consys.core.store.cassandra.LockingStoreExt.ZookeeperLock

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

		override def replicateRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T) : StoreType#RawType[T] = {
			val lock = store.retrieveLockFor(addr)
			lock.acquire()

			new StrongCassandraObject(addr, obj, store, lock)
		}

		override def lookupRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr) : StoreType#RawType[T] = {
			val lock = store.retrieveLockFor(addr)
			lock.acquire()

			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ALL)
			new StrongCassandraObject(addr, raw, store, lock)
		}
	}

	private class StrongCassandraObject[T <: java.io.Serializable : TypeTag](override val addr : String, override val state : T, store : StoreType, lock : ZookeeperLock) extends CassandraObject[T] {
		override def consistencyLevel : StoreConsistencyLevel { type StoreType = CassandraStore } = Strong

		override def commit() : Unit = {
			store.CassandraBinding.writeObject(addr, state, CLevel.ALL)
			lock.release()
		}
	}

}