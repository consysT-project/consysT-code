package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag

/**
 * Trait for transaction contexts to be used with a certain store type. Transaction
 * contexts store information about the current transaction.
 *
 * Transaction contexts are provided to developers when they start a transaction, and
 * are used for interacting with the replicated store.
 */
trait TransactionContext[StoreType <: Store] {
	val store : StoreType

	def replicate[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level, constructorArgs : Any*) : StoreType#RefType[T]
	def lookup[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level) : StoreType#RefType[T]


	/* Java interface for replicate */
	final def replicate[T <: StoreType#ObjType](addr : StoreType#Addr, level : StoreType#Level, clazz : Class[T], constructorArgs : Array[Any]) : StoreType#RefType[T] = {
		replicate(addr, level, constructorArgs : _*)(ClassTag(clazz))
	}
	/* Java interface for lookup */
	final def lookup[T <: StoreType#ObjType](addr : StoreType#Addr, level : StoreType#Level, clazz : Class[T]) : StoreType#RefType[T] = {
		lookup(addr, level)(ClassTag(clazz))
	}
}


