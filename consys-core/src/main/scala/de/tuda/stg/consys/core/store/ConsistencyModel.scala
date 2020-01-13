package de.tuda.stg.consys.core.store

import scala.reflect.runtime.universe._

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait ConsistencyModel {
	type StoreType <: Store

	def toLevel : ConsistencyLevel
	def createRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T) : StoreType#RefType[T]
	def lookupRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr) : StoreType#RefType[T]
}
