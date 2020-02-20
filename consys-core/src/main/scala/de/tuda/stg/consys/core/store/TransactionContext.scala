package de.tuda.stg.consys.core.store

import java.lang.reflect.Constructor

import akka.util.BoxedType
import de.tuda.stg.consys.core.store.legacy.ConsysUtils
import de.tuda.stg.consys.core.store.utils.Reflect

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag
import scala.util.Try

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait TransactionContext {
	type StoreType <: Store
	type ConsistencyLevel =  StoreConsistencyLevel {type StoreType = TransactionContext.this.StoreType}

	val store : StoreType

	final def replicate[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : ConsistencyLevel, constructorArgs : Any*) : StoreType#RefType[T] = {
		val obj = callConstructor(implicitly[ClassTag[T]], constructorArgs : _*)

		store.enref(
			replicateRaw[T](addr, obj, level)(implicitly[ClassTag[T]])
				.asInstanceOf[store.RawType[T with store.ObjType]]
		).asInstanceOf[StoreType#RefType[T]]
	}

	final def lookup[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		store.enref(
			lookupRaw[T](addr, level)(implicitly[ClassTag[T]])
				.asInstanceOf[store.RawType[T with store.ObjType]]
		).asInstanceOf[StoreType#RefType[T]]

	private[store] def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support replication.")

	private[store] def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support lookups.")


	/* Java interface for replicate */
	final def replicate[T <: StoreType#ObjType](addr : StoreType#Addr, level : ConsistencyLevel, clazz : Class[T], constructorArgs : Array[Any]) : StoreType#RefType[T] = {
		replicate(addr, level, constructorArgs : _*)(ClassTag(clazz))
	}
	/* Java interface for ref */
	final def lookup[T <: StoreType#ObjType](addr : StoreType#Addr, l : ConsistencyLevel, clazz : Class[T]) : StoreType#RefType[T] = {
		lookup(addr, l)(ClassTag(clazz))
	}

	private def callConstructor[T](clazz : ClassTag[T], args : Any*) : T = {
		val constructor = Reflect.findConstructor(clazz.runtimeClass, args : _*)
		constructor.newInstance(args.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[T]
	}


}


