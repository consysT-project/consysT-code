package de.tuda.stg.consys.core.store.akka.levels

import akka.actor.ActorRef
import de.tuda.stg.consys.core.store.akka.Requests._
import de.tuda.stg.consys.core.store.akka.{AkkaObject, AkkaStore, AkkaStores}

import scala.collection.mutable
import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Weak extends AkkaConsistencyLevel {
	override def toProtocol(store : StoreType) : Protocol = new WeakProtocol(store)

	private class WeakProtocol(val store : AkkaStore) extends AkkaConsistencyProtocol {
		override def toLevel : Level = Weak

		def createMasterReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#HandlerType[T] = {
			new WeakMasterAkkaObject[T](addr, obj, store, txContext)
		}

		def createFollowerReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, masterRef : ActorRef, txContext : StoreType#TxContext) : StoreType#HandlerType[T] = {
			new WeakFollowerAkkaObject[T](addr, obj, store, masterRef, txContext)
		}
	}


	private class WeakMasterAkkaObject[T <: StoreType#ObjType : ClassTag](override val addr : String, private var internalState : T, store : StoreType, txContext : StoreType#TxContext) extends AkkaObject[T] {
		override def consistencyLevel : AkkaStore#Level = Weak

		override def state : T = internalState

		override def invoke[R](methodName: String, args: Seq[Seq[Any]]) : R = {
			super.invoke(methodName, args)
		}

		override def getField[R](fldName : String) : R = {
			super.getField(fldName)
		}

		override def setField[R](fldName : String, newVal : R) : Unit = {
			super.setField(fldName, newVal)
		}

		def sync() : Unit = {
			//super.internalSync()
			println("WARNING: sync on master")
		}

		override def handleRequest[R](request : Request[R]) : R = request match {
			case SynchronizeWithWeakMaster(ops) =>
				ops.foreach(op => {
					AkkaStores.currentTransaction.withValue (null /* replicaSystem.setCurrentTransaction(op.tx) */) {
						op match {
							case InvokeOp(path, mthdName, args) => invoke[Any](mthdName, args)
							case SetFieldOp(path, fldName, newVal) => setField(fldName, newVal)
							case GetFieldOp(_, _) => throw new IllegalStateException("get field operations are not needed to be applied.")
						}
					}
				})
				WeakSynchronized(state).asInstanceOf[R]
			case _ =>
				super.handleRequest(request)
		}

		override def toString : String = s"WeakMaster($addr, $state)"
	}

	private class WeakFollowerAkkaObject[T <: StoreType#ObjType : ClassTag](override val addr : String, private var internalState : T, store : StoreType, masterRef : ActorRef, txContext : StoreType#TxContext) extends AkkaObject[T] {
		override def consistencyLevel : AkkaStore#Level = Weak

		override def state : T = internalState

		private val unsynchronized : mutable.Buffer[Operation[_]] = mutable.Buffer.empty

		override def invoke[R](methodName: String, args: Seq[Seq[Any]]) : R = {
			unsynchronized += InvokeOp("lol", methodName, args)
			super.invoke(methodName, args)
		}

		override def getField[R](fldName : String) : R = {
			super.getField(fldName)
		}

		override def setField[R](fldName : String, newVal : R) : Unit = {
			unsynchronized += SetFieldOp("xD", fldName, newVal)
			super.setField(fldName, newVal)
		}


		def sync() : Unit = {
			val handler = store.handlerFor(masterRef)

			val WeakSynchronized(newObj : T@unchecked) =
				handler.request(addr, SynchronizeWithWeakMaster(unsynchronized))
			handler.close()

			internalState = newObj
			unsynchronized.clear()
		}

		override def toString : String = s"WeakFollower($addr, $state)"
	}


	case class SynchronizeWithWeakMaster(seq : scala.collection.Seq[Operation[_]]) extends SynchronousRequest[WeakSynchronized]
	case class WeakSynchronized(obj : Any)

}




