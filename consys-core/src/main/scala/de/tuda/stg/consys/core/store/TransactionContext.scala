package de.tuda.stg.consys.core.store

import de.tuda.stg.consys.core.store

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait TransactionContext {
	type StoreType <: Store
	type ConsistencyLevel =  StoreConsistencyLevel {type StoreType = TransactionContext.this.StoreType}

	val store : StoreType

	def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] =
		throw new UnsupportedOperationException("this transaction context does not support replication.")

	def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		throw new UnsupportedOperationException("this transaction context does not support lookups.")


}
