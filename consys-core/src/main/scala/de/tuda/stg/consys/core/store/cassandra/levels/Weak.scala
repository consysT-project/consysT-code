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
case object Weak extends CassandraConsistencyLevel {
	override def toModel(store : StoreType) : Model = new WeakModel(store)

	private class WeakModel(val store : CassandraStore) extends CassandraConsistencyModel {
		override def toLevel : Level = Weak

		override def writeRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			val cassObj = new WeakCassandraObject(addr, obj, store, txContext)
			cassObj
		}

		override def readRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
			val raw = store.CassandraBinding.readObject[T](addr, ConsistencyLevel.ONE)
			new WeakCassandraObject(addr, raw, store, txContext)
		}
	}


	private class WeakCassandraObject[T <: StoreType#ObjType : ClassTag](override val addr : String, override val state : T, store : StoreType, txContext : StoreType#TxContext) extends CassandraObject[T] {
		override def consistencyLevel : CassandraStore#Level = Weak

		override protected[cassandra] def writeToStore(store : CassandraStore) : Unit =
			store.CassandraBinding.writeObject(addr, state, ConsistencyLevel.ONE, txContext.timestamp)
	}
}