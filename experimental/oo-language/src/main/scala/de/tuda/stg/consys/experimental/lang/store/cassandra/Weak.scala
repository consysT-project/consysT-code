package de.tuda.stg.consys.experimental.lang.store.cassandra

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}
import de.tuda.stg.consys.experimental.lang.store.{ConsistencyLevel, ConsistencyModel}

import scala.reflect.runtime.universe._

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Weak extends ConsistencyLevel {
	override type StoreType = CassandraStore
	override def toModel(store : StoreType) : ConsistencyModel {type StoreType = Weak.this.StoreType} = new Model(store)

	private class Model(val store : CassandraStore) extends ConsistencyModel {
		override type StoreType = CassandraStore

		override def toLevel : ConsistencyLevel = Weak

		override def createRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T) : StoreType#RefType[T] = {
			val cassObj = new WeakCassandraObject(addr, obj, store)
			CassandraHandler(cassObj)
		}

		override def lookupRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr) : StoreType#RefType[T] = {
			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ONE)
			createRef(addr, raw)
		}
	}


	private class WeakCassandraObject[T <: java.io.Serializable : TypeTag](addr : String, state : T, store : StoreType) extends CassandraObject[T](addr, state) {
		override def commit() : Unit = {
			store.CassandraBinding.writeObject(addr, state, CLevel.ONE)
		}
	}
}