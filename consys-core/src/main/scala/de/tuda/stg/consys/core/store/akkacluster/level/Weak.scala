package de.tuda.stg.consys.core.store.akkacluster.level

import de.tuda.stg.consys.core.store.akkacluster.{AkkaClusterCachedObject, AkkaClusterRef, AkkaClusterStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}

import scala.reflect.ClassTag


case object Weak extends ConsistencyLevel[AkkaClusterStore] {
	override def toProtocol(store : AkkaClusterStore) : ConsistencyProtocol[AkkaClusterStore, Weak.type] =
		new WeakProtocol(store)

	private class WeakProtocol(val store : AkkaClusterStore) extends ConsistencyProtocol[AkkaClusterStore, Weak.type] {
		override def toLevel : Weak.type = Weak

		override def replicate[T <: AkkaClusterStore#ObjType : ClassTag](
			txContext : AkkaClusterStore#TxContext,
			addr : AkkaClusterStore#Addr,
			obj : T
		) : AkkaClusterStore#RefType[T] = {
			txContext.Cache.addEntry(addr, AkkaClusterCachedObject[T](addr, obj, Weak))
			AkkaClusterRef[T](addr, Weak)
		}

		override def lookup[T <: AkkaClusterStore#ObjType : ClassTag](
			txContext : AkkaClusterStore#TxContext,
			addr : AkkaClusterStore#Addr
		) : AkkaClusterStore#RefType[T] = {
			AkkaClusterRef[T](addr, Weak)
		}

		override def invoke[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
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

		override def getField[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			val entry = txContext.Cache.readEntry(addr, weakRead[T](addr))
			val result = entry.getField[R](fieldName)
			result
		}

		override def setField[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
			fieldName : String,
			value : R
		) : Unit = {
			val addr = receiver.addr
			val entry = txContext.Cache.readEntry(addr, weakRead[T](addr))
			entry.setField[R](fieldName, value)
			txContext.Cache.setFieldsChanged(addr, Iterable.single(Reflect.getField(implicitly[ClassTag[T]].runtimeClass, fieldName)))
		}

		private def weakRead[T <: AkkaClusterStore#ObjType : ClassTag](addr: AkkaClusterStore#Addr) : AkkaClusterCachedObject[T] = {
			val state = store.replica.readLocal[T](addr)
			AkkaClusterCachedObject(addr, state, Weak)
		}
	}
}