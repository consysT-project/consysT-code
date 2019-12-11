package de.tuda.stg.consys.experimental.lang.store


import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait TxContext {
	type StoreType <: Store
	type ConsistencyLevel =  de.tuda.stg.consys.experimental.lang.store.ConsistencyLevel {type StoreType = TxContext.this.StoreType}

	val store : StoreType
	import store._

	def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] =
		throw new UnsupportedOperationException("this context does not support replicating new objects")

	def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] =
		throw new UnsupportedOperationException("this context does not support looking up existing objects")

}
