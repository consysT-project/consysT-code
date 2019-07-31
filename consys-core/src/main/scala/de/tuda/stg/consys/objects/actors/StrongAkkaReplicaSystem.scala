package de.tuda.stg.consys.objects.actors

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.Strong
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.Strong
import de.tuda.stg.consys.objects.Utils.TxMutex
import de.tuda.stg.consys.objects.actors.Requests._
import de.tuda.stg.consys.objects.actors.StrongAkkaReplicaSystem.StrongReplicatedObject.{StrongFollowerReplicatedObject, StrongMasterReplicatedObject}

import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.DynamicVariable


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait StrongAkkaReplicaSystem[Addr] extends AkkaReplicaSystem[Addr] {

	override protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Strong => new StrongMasterReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Strong => new StrongFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}

object StrongAkkaReplicaSystem {

	trait StrongReplicatedObject[Addr, T <: AnyRef]
		extends AkkaReplicatedObject[Addr, T]
		with LockableReplicatedObject[T] {
		override final def consistencyLevel : ConsistencyLevel = Strong
	}


	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Addr, T]
			with AkkaMultiversionReplicatedObject[Addr, T] {
			setObject(init)

			private val txMutex = new TxMutex()

			private[actors] def lock(txid : Long) : Unit = {
				txMutex.lockTxid(txid)
			}

			private[actors] def unlock(txid : Long) : Unit = {
				txMutex.unlockTxid(txid)
			}

			override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				tx.isToplevel
				val res = super.internalInvoke[R](tx, methodName, args)
				res
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				val result = super.internalGetField[R](tx, fldName)
				result
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(tx, fldName, newVal)
			}

			override def internalSync() : Unit = {

			}

			override def handleRequest(request : Request) : Any = request match {
				case LockReq(txid) =>
					lock(txid)
					LockRes(getObject)

				case MergeReq(null, op, result) =>
					cache(op, result)
					()

				case MergeReq(newObj : T@unchecked, op, result) =>
					setObject(newObj)
					cache(op, result)
					()

				case UnlockReq(txid) =>
					unlock(txid)
					()

				case _ => super.handleRequest(request)
			}

			override protected def transactionStarted(tx : Transaction) : Unit = {
				if (opCache.contains(tx)) {
					//transaction is cached. No locking required.
				} else {
					lock(tx.txid)
					tx.addLock(addr.asInstanceOf[String])
				}
				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				super.transactionFinished(tx)
			}

			override def toString : String = s"StrongMaster($addr, $getObject)"
		}


		class StrongFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Addr, T]
			//TODO: Multiversion on follower? How to GC this?
			with AkkaMultiversionReplicatedObject[Addr, T] {
			setObject(init)

			//Handles communication with the master
			private var handler : DynamicVariable[RequestHandler[Addr]] = new DynamicVariable(null)

			override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				val res = super.internalInvoke[R](tx, methodName, args)
				handler.value.request(addr, MergeReq(getObject, InvokeOp(tx, methodName, args), res))

				res
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				val res = super.internalGetField[R](tx, fldName)
				handler.value.request(addr,  MergeReq(null, GetFieldOp(tx, fldName), res))

				res
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(tx, fldName, newVal)
				handler.value.request(addr, MergeReq(getObject, SetFieldOp(tx, fldName, newVal), ()))
			}

			override def internalSync() : Unit = {	}



			override private[actors] def lock(txid : Long) : Unit = {
				lockWithHandler(txid, replicaSystem.acquireHandlerFrom(masterReplica))
			}

			override private[actors] def unlock(txid : Long) : Unit = {
				unlockWithHandler(txid, replicaSystem.acquireHandlerFrom(masterReplica))
			}

			private def lockWithHandler(txid : Long, handler : RequestHandler[Addr]) : Unit = {
				val LockRes(masterObj : T@unchecked) = handler.request(addr, LockReq(txid))
				setObject(masterObj)
			}

			private def unlockWithHandler(txid : Long, handler : RequestHandler[Addr]) : Unit = {
				handler.request(addr, UnlockReq(txid))
			}

			override def toString : String = s"StrongFollower($addr, $getObject)"


			override protected def transactionStarted(tx : Transaction) : Unit = {
				assert(handler.value == null)

				handler.value = replicaSystem.acquireHandlerFrom(masterReplica)

				if (opCache.contains(tx)) {
					//transaction is cached. No locking required.
				} else {
					lockWithHandler(tx.txid, handler.value)
					tx.addLock(addr.asInstanceOf[String])
				}

				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				handler.value.close()
				handler.value = null

				super.transactionFinished(tx)
			}



		}
	}



	sealed trait StrongReq extends Request
	case class LockReq(txid : Long) extends StrongReq with ReturnRequest
	case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
	case class MergeReq(obj : AnyRef, op : Operation[Any], result : Any) extends StrongReq with ReturnRequest
	case class UnlockReq(txid : Long) extends StrongReq with ReturnRequest

}
