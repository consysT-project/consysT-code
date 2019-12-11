package de.tuda.stg.consys.experimental.lang.store.cassandra

import de.tuda.stg.consys.experimental.lang.store.{ConsistencyLevel, ConsistencyModel}

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
object Weak extends ConsistencyLevel {
	override type StoreType = CassandraStore
	override def toModel(store : StoreType) : ConsistencyModel {type StoreType = Weak.this.StoreType} = new Model(store)

	class Model(override val store : CassandraStore) extends ConsistencyModel {
		override type StoreType = CassandraStore

		import store._

		override def toLevel : ConsistencyLevel = Weak

		override def createLocal[T <: ObjType](addr :Addr, obj : T) : RefType[T] = {
			???
		}
	}
}