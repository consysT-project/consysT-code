package de.tudarmstadt.consistency.replobj.actors

import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.locks.{ReentrantLock, ReentrantReadWriteLock}

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevel
import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Strong
import de.tudarmstadt.consistency.replobj.actors.Requests._
import de.tudarmstadt.consistency.replobj.actors.StrongAkkaReplicaSystem.StrongReplicatedObject.{StrongFollowerReplicatedObject, StrongMasterReplicatedObject}

import scala.language.postfixOps
import scala.reflect.runtime.universe._


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
		//Strong objects cache their results for MVCC
		with AkkaMultiversionReplicatedObject[Addr, T] {

		override final def consistencyLevel : ConsistencyLevel = Strong
	}


	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Addr, T] {
			setObject(init)


			val lock = new ReentrantLock()
//			val txMutex = new TxMutex

			override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				val res = super.internalInvoke[R](opid, methodName, args)
				res
			}

			override def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				val result = super.internalGetField[R](opid, fldName)
				result
			}

			override def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(opid, fldName, newVal)
			}

			override def internalSync() : Unit = {

			}

			override def handleRequest(request : Request) : Any = request match {
				case LockReq(txid) =>
					lock.lock()
					LockRes(getObject)

				case MergeAndUnlock(txid, null, op, result) =>
					cache(op, result)
					lock.unlock()

				case MergeAndUnlock(txid, newObj : T, op, result) =>
					setObject(newObj)
					cache(op, result)
					lock.unlock()

				case ReadStrongField(GetFieldOp(path, fldName)) =>
					ReadResult(internalGetField(path, fldName))

				case _ => super.handleRequest(request)
			}

			override protected def toplevelTransactionStarted(ctx : ContextPath) : Unit = {
//				txMutex.lockFor(ctx.txid)
				lock.lock()
			}

			override protected def nestedTransactionStarted(ctx : ContextPath) : Unit = {
//				txMutex.lockFor(ctx.txid)
				lock.lock()
			}

			override protected def nestedTransactionFinished(ctx : ContextPath) : Unit = {
//				txMutex.unlockFor(ctx.txid)
				lock.unlock()
			}

			override protected def toplevelTransactionFinished(ctx : ContextPath) : Unit = {
//				txMutex.unlockFor(ctx.txid)
				lock.unlock()
			}

			override def toString : String = s"StrongMaster($addr, $getObject)"
		}


		class StrongFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Addr, T] {
			setObject(init)


			override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				val res = super.internalInvoke[R](opid, methodName, args)
				handler.request(addr, MergeAndUnlock(opid.txid, getObject, InvokeOp(opid, methodName, args), res))
				handler.close()
				res
			}

			override def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				val res = super.internalGetField[R](opid, fldName)

				val mergeReq = MergeAndUnlock(opid.txid, null, GetFieldOp(opid, fldName), res)
				handler.request(addr, mergeReq)
				handler.close()

				res
			}

			override def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				super.internalSetField(opid, fldName, newVal)

				val mergeReq = MergeAndUnlock(opid.txid, getObject, SetFieldOp(opid, fldName, newVal), ())
				handler.request(addr, mergeReq)
				handler.close()
			}

			override def internalSync() : Unit = {	}

			override def toString : String = s"StrongFollower($addr, $getObject)"
		}
	}





	sealed trait StrongReq extends Request
	case class LockReq(txid : Long) extends StrongReq with ReturnRequest
	case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
	case class MergeAndUnlock(txid : Long, obj : AnyRef, op : Operation[Any], result : Any) extends StrongReq with ReturnRequest
	case class ReadStrongField(op : GetFieldOp[Any]) extends StrongReq with ReturnRequest



//	private case object SynchronizeWithStrongMaster extends StrongReq with ReturnRequest
//
//	private case class StrongSynchronized[T <: AnyRef](obj : T)
	case class ReadResult(res : Any)



	case object MergeAck

}
