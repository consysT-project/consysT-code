package de.tuda.stg.consys.experimental.lang.store.cassandra

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}
import de.tuda.stg.consys.experimental.lang.store.cassandra.LockingStoreExt.ZookeeperLock
import de.tuda.stg.consys.experimental.lang.store.{ConsistencyLevel, ConsistencyModel}

import scala.reflect.runtime.universe._

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Strong extends ConsistencyLevel {
	override type StoreType = CassandraStore
	override def toModel(store : StoreType) : ConsistencyModel {type StoreType = Strong.this.StoreType} = new Model(store)

	private class Model(val store : CassandraStore) extends ConsistencyModel {
		override type StoreType = CassandraStore

		override def toLevel : ConsistencyLevel = Strong

		override def createRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T) : StoreType#RefType[T] = {
			val lock = store.lockFor(addr)
			lock.acquire()

			val cassObj = new StrongCassandraObject(addr, obj, store, lock)
			CassandraHandler(cassObj)
		}

		override def lookupRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr) : StoreType#RefType[T] = {
			val lock = store.lockFor(addr)
			lock.acquire()

			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ALL)
			val cassObj = new StrongCassandraObject(addr, raw, store, lock)
			CassandraHandler(cassObj)
		}
	}

	private class StrongCassandraObject[T <: java.io.Serializable : TypeTag](addr : String, state : T, store : StoreType, lock : ZookeeperLock) extends CassandraObject[T](addr, state) {
		override def commit() : Unit = {
			store.CassandraBinding.writeObject(addr, state, CLevel.ALL)
			lock.release()
		}
	}

}