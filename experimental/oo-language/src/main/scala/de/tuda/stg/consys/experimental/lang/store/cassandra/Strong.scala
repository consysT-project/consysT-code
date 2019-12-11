package de.tuda.stg.consys.experimental.lang.store.cassandra

import de.tuda.stg.consys.experimental.lang.store.{ConsistencyLevel, ConsistencyModel}
import com.datastax.oss.driver.api.core.{ConsistencyLevel => CLevel}

import scala.reflect.runtime.universe
import scala.reflect.runtime.universe._

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Strong extends ConsistencyLevel {
	override type StoreType = CassandraStore
	override def toModel(store : StoreType) : ConsistencyModel {type StoreType = Strong.this.StoreType} = new Model(store)

	private class Model(override val store : CassandraStore) extends ConsistencyModel {
		override type StoreType = CassandraStore
		import store._

		override def toLevel : ConsistencyLevel = Strong

		override def createRef[T <: ObjType : TypeTag](addr :Addr, obj : T) : RefType[T] = {
			val cassObj = new StrongObject(addr, obj)
			CassandraHandler(cassObj)
		}

		override def lookupRef[T <: ObjType : TypeTag](addr :Addr) : RefType[T] = {
			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ALL)
			createRef(addr, raw)
		}
	}

	private class StrongObject[T <: Serializable : TypeTag](addr : String, state : T) extends CassandraObject[T](addr, state)
}