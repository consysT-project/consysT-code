package de.tuda.stg.consys.core.store

import de.tuda.stg.consys.core.{ConsysUtils, store}

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

	final def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] = {
		store.enref(
			replicateRaw[T](addr, obj, level)(implicitly[TypeTag[T]])
				.asInstanceOf[store.RawType[T with store.ObjType]]
		).asInstanceOf[StoreType#RefType[T]]
	}

	final def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		store.enref(
			lookupRaw[T](addr, level)(implicitly[TypeTag[T]])
				.asInstanceOf[store.RawType[T with store.ObjType]]
		).asInstanceOf[StoreType#RefType[T]]

	private[store] def replicateRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support replication.")

	private[store] def lookupRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support lookups.")


	/* Java interface for replicate */
	final def replicate[T <: StoreType#ObjType](addr : StoreType#Addr, obj : T, objCls : Class[T], level : ConsistencyLevel) : StoreType#RefType[T] = {
		replicate(addr, obj, level)(ConsysUtils.typeTagFromCls(objCls))
	}
	/* Java interface for ref */
	final def lookup[T <: StoreType#ObjType](addr : StoreType#Addr, objCls : Class[T], l : ConsistencyLevel) : StoreType#RefType[T] = {
		lookup(addr, l)(ConsysUtils.typeTagFromCls(objCls))
	}

}


