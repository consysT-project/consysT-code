package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevel
import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Strong
import de.tudarmstadt.consistency.replobj.Utils.TxMutex
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
		extends AkkaReplicatedObject[Addr, T]	{
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

			//TODO: Implement correct 2PL
			private val txMutex = new TxMutex()

			private def lock(txid : Long) : Unit = {
				txMutex.lockTxid(txid)
			}

			private def unlock(txid : Long) : Unit = {
				txMutex.unlockTxid(txid)
			}

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
					lock(txid)
					LockRes(getObject)

				case MergeReq(null, op, result) =>
					cache(op, result)
					()

				case MergeReq(newObj : T, op, result) =>
					setObject(newObj)
					cache(op, result)
					()

				case UnlockReq(txid) =>
					unlock(txid)
					()


				case _ => super.handleRequest(request)
			}

			override protected def toplevelTransactionStarted(ctx : ContextPath) : Unit = {
				lock(ctx.txid)
			}

			override protected def nestedTransactionStarted(ctx : ContextPath) : Unit = {
				lock(ctx.txid)
			}

			override protected def nestedTransactionFinished(ctx : ContextPath) : Unit = {
				unlock(ctx.txid)
			}

			override protected def toplevelTransactionFinished(ctx : ContextPath) : Unit = {
				unlock(ctx.txid)
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


			override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				val res = super.internalInvoke[R](opid, methodName, args)

				handler.request(addr, MergeReq(getObject, InvokeOp(opid, methodName, args), res))
				handler.request(addr, UnlockReq(opid.txid))
				handler.close()
				res
			}

			override def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				val res = super.internalGetField[R](opid, fldName)

				handler.request(addr,  MergeReq(null, GetFieldOp(opid, fldName), res))
				handler.request(addr, UnlockReq(opid.txid))
				handler.close()

				res
			}

			override def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq(opid.txid))
				setObject(masterObj)
				super.internalSetField(opid, fldName, newVal)

				handler.request(addr, MergeReq(getObject, SetFieldOp(opid, fldName, newVal), ()))
				handler.request(addr, UnlockReq(opid.txid))
				handler.close()
			}

			override def internalSync() : Unit = {	}

			override def toString : String = s"StrongFollower($addr, $getObject)"
		}
	}



	sealed trait StrongReq extends Request
	case class LockReq(txid : Long) extends StrongReq with ReturnRequest
	case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
	case class MergeReq(obj : AnyRef, op : Operation[Any], result : Any) extends StrongReq with ReturnRequest
	case class UnlockReq(txid : Long) extends StrongReq with ReturnRequest

}
