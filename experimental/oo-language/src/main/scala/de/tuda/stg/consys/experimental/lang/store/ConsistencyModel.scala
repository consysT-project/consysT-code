package de.tuda.stg.consys.experimental.lang.store

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

	def createLocal[T <: ObjType](addr : Addr, obj : T) : RefType[T]

}
