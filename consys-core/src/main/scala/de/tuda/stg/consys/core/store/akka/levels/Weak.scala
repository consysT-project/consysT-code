package de.tuda.stg.consys.core.store.akka.levels

import de.tuda.stg.consys.core.store.akka.{AkkaCachedObject, AkkaRef, AkkaStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}

import scala.reflect.ClassTag


case object Weak extends ConsistencyLevel[AkkaStore] {
	override def toProtocol(store : AkkaStore) : ConsistencyProtocol[AkkaStore, Weak.type] =
		new WeakProtocol(store)

	private class WeakProtocol(val store : AkkaStore) extends ConsistencyProtocol[AkkaStore, Weak.type] {
		override def toLevel : Weak.type = Weak

		override def replicate[T <: AkkaStore#ObjType : ClassTag](
			txContext : AkkaStore#TxContext,
			addr : AkkaStore#Addr,
			obj : T
		) : AkkaStore#RefType[T] = {
			txContext.Cache.addEntry(addr, AkkaCachedObject[T](addr, obj, Weak))
			AkkaRef[T](addr, Weak)
		}

		override def lookup[T <: AkkaStore#ObjType : ClassTag](
			txContext : AkkaStore#TxContext,
			addr : AkkaStore#Addr
		) : AkkaStore#RefType[T] = {
			AkkaRef[T](addr, Weak)
		}

		override def invoke[T <: AkkaStore#ObjType : ClassTag, R](
			txContext : AkkaStore#TxContext,
			receiver : AkkaStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val addr = receiver.addr
			val entry  = txContext.Cache.readEntry[T](addr, weakRead[T](addr))
			val result = entry.invoke[R](methodId, args)

			//If method call is not side effect free, then set the changed flag
			val (objectChanged, changedFields) = Reflect.getMethodSideEffects[T](methodId, args)

			if (objectChanged) txContext.Cache.setObjectChanged(addr)
			if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

			result
		}

		override def getField[T <: AkkaStore#ObjType : ClassTag, R](
			txContext : AkkaStore#TxContext,
			receiver : AkkaStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			val entry = txContext.Cache.readEntry(addr, weakRead[T](addr))
			val result = entry.getField[R](fieldName)
			result
		}

		override def setField[T <: AkkaStore#ObjType : ClassTag, R](
			txContext : AkkaStore#TxContext,
			receiver : AkkaStore#RefType[T],
			fieldName : String,
			value : R
		) : Unit = {
			val addr = receiver.addr
			val entry = txContext.Cache.readEntry(addr, weakRead[T](addr))
			entry.setField[R](fieldName, value)
			txContext.Cache.setFieldsChanged(addr, Iterable.single(Reflect.getField(implicitly[ClassTag[T]].runtimeClass, fieldName)))
		}

		private def weakRead[T <: AkkaStore#ObjType : ClassTag](addr: AkkaStore#Addr) : AkkaCachedObject[T] = {
			val state = store.replica.read[T](addr)
			AkkaCachedObject(addr, state, Weak)
		}
	}
}