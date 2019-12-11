package de.tuda.stg.consys.experimental.lang.store

import scala.reflect.runtime.universe._

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait ConsistencyModel {
	type StoreType <: Store
	val store : StoreType

	import store._
	def toLevel : ConsistencyLevel
	def createRef[T <: ObjType : TypeTag](addr : Addr, obj : T) : RefType[T]
	def lookupRef[T <: ObjType : TypeTag](addr : Addr) : RefType[T]
}
