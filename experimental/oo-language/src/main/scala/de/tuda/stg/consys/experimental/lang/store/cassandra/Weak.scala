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

	private class Model(override val store : CassandraStore) extends ConsistencyModel {
		override type StoreType = CassandraStore
		import store._

		override def toLevel : ConsistencyLevel = Weak

		override def createRef[T <: ObjType : TypeTag](addr :Addr, obj : T) : RefType[T] = {
			val cassObj = new WeakObject(addr, obj)
			CassandraHandler(cassObj)
		}

		override def lookupRef[T <: ObjType : TypeTag](addr :Addr) : RefType[T] = {
			val raw = store.CassandraBinding.readObject[T](addr, CLevel.ONE)
			createRef(addr, raw)
		}
	}

	private class WeakObject[T <: java.io.Serializable : TypeTag](addr : String, state : T) extends CassandraObject[T](addr, state)
}