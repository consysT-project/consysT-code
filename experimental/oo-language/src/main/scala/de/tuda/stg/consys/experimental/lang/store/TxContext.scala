package de.tuda.stg.consys.experimental.lang.store

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait TxContext {
	type StoreType <: Store

	val store : StoreType
	import store._

	def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] = ???

	def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] = ???

}
