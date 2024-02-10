package de.tuda.stg.consys.core.store.akkacluster.level

import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterCachedObject.{ReadStrong, ReadWeak}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}
import de.tuda.stg.consys.core.store.akkacluster.{AkkaClusterCachedObject, AkkaClusterRef, AkkaClusterStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.logging.Logger

import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Mixed extends ConsistencyLevel[AkkaClusterStore] {
	override def toProtocol(store : AkkaClusterStore) : ConsistencyProtocol[AkkaClusterStore, Mixed.type] =
		new MixedProtocol(store)

	private class MixedProtocol(val store : AkkaClusterStore) extends ConsistencyProtocol[AkkaClusterStore, Mixed.type] {
		override def toLevel : Mixed.type = Mixed

		override def replicate[T <: AkkaClusterStore#ObjType : ClassTag](
			txContext : AkkaClusterStore#TxContext,
			addr : AkkaClusterStore#Addr,
			obj : T
		) : AkkaClusterStore#RefType[T] = {
			txContext.Cache.addEntry(addr, AkkaClusterCachedObject[T](addr, obj, Mixed, ReadStrong))
			AkkaClusterRef[T](addr, Mixed)
		}

		override def lookup[T <: AkkaClusterStore#ObjType : ClassTag](
			txContext : AkkaClusterStore#TxContext,
			addr : AkkaClusterStore#Addr
		) : AkkaClusterStore#RefType[T] = {
			AkkaClusterRef[T](addr, Mixed)
		}

		override def invoke[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val flattenedArgs = args.flatten
			val clazz = implicitly[ClassTag[T]]
			val method = Reflect.getMethod[T](clazz.runtimeClass.asInstanceOf[Class[T]], methodId, flattenedArgs : _*)

			/* Execute a strong method */
			if (method.getAnnotation(classOf[StrongOp]) != null) {


				val addr = receiver.addr
				txContext.acquireLock(addr)

				var entry = txContext.Cache.readEntry[T](addr, strongRead[T](addr))
				if (entry.readLevel == ReadWeak) {
					val obj = strongRead[T](addr)
					//TODO: Only update strong fields, and leave weak fields untouched
					txContext.Cache.updateEntry(addr, obj, false, Iterable.empty)
					entry = obj
				}


				val result = entry.invoke[R](methodId, args)

				//If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Reflect.getMethodSideEffects[T](methodId, args)

				if (objectChanged) txContext.Cache.setObjectChanged(addr)
				if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

				result
			} else /* if (method.getAnnotation(classOf[WeakOp]) != null) */ { //TODO: Resolve default operation types
				if (method.getAnnotation(classOf[WeakOp]) == null) {
					Logger.info(s"Warning: Method [${method.toString}] executed with Weak consistency because it was not annotated.")
				}


				val addr = receiver.addr
				val entry  = txContext.Cache.readEntry[T](addr, weakRead[T](addr))
				val result = entry.invoke[R](methodId, args)

				//If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Reflect.getMethodSideEffects[T](methodId, args)

				if (objectChanged) txContext.Cache.setObjectChanged(addr)
				if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

				result

			}
		}

		override def getField[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
			fieldName : String
		) : R = {
			throw new UnsupportedOperationException("field reads are not supported by Mixed consistency")
		}

		override def setField[T <: AkkaClusterStore#ObjType : ClassTag, R](
			txContext : AkkaClusterStore#TxContext,
			receiver : AkkaClusterStore#RefType[T],
			fieldName : String, value : R
		) : Unit = {
			throw new UnsupportedOperationException("field writes are not supported by Mixed consistency")
		}


		private def strongRead[T <: AkkaClusterStore#ObjType : ClassTag](addr: AkkaClusterStore#Addr) : AkkaClusterCachedObject[T] = {
			val state = store.replica.readAll[T](addr)
			AkkaClusterCachedObject(addr, state, Mixed, ReadStrong)
		}

		private def weakRead[T <: AkkaClusterStore#ObjType : ClassTag](addr: AkkaClusterStore#Addr) : AkkaClusterCachedObject[T] = {
			val state = store.replica.readLocal[T](addr)
			AkkaClusterCachedObject(addr, state, Mixed, ReadWeak)
		}



	}
}