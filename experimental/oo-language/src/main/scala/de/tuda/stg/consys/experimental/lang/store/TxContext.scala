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


	def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] =
		level.toModel(store).createRef[T](addr, obj)

	def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		level.toModel(store).lookupRef[T](addr)

}
