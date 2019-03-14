package de.tudarmstadt.consistency.replobj.actors

import java.util.concurrent.locks.ReentrantLock

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevels
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Strong
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

	override protected def createMasterReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T, L] = {
		if (ConsistencyLevels.isStrong[L])
		//We have to cast here because the type system can not infer L == Strong
			new StrongMasterReplicatedObject[Addr, T](obj, addr, this).asInstanceOf[AkkaReplicatedObject[Addr, T, L]]
		else
			super.createMasterReplica[T, L](addr, obj)
	}

	override protected def createFollowerReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T, L] = {
		if (ConsistencyLevels.isStrong[L])
		//We have to cast here because the type system can not infer L == Strong
			new StrongFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this).asInstanceOf[AkkaReplicatedObject[Addr, T, L]]
		else
			super.createFollowerReplica[T, L](addr, obj, masterRef)
	}
}

object StrongAkkaReplicaSystem {

	trait StrongReplicatedObject[Addr, T <: AnyRef]
		extends AkkaReplicatedObject[Addr, T, Strong]
		//Strong objects cache their results for MVCC
		with AkkaMultiversionReplicatedObject[Addr, T, Strong]


	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Strong]
		) extends StrongReplicatedObject[Addr, T] {
			setObject(init)

			private val lock : ReentrantLock = new ReentrantLock()

			protected override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				lock.lock()
				val res = super.internalInvoke[R](opid, methodName, args)
				lock.unlock()
				res
			}

			override protected def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				/*get is not synchronized*/
				super.internalGetField[R](opid, fldName)
			}

			override protected def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				lock.lock()
				super.internalSetField(opid, fldName, newVal)
				lock.unlock()
			}

			override def handleRequest(request : Request) : Any = request match {
				case LockReq =>
					lock.lock()
					LockRes(getObject)

				case MergeAndUnlock(newObj : T, op, result) =>
					setObject(newObj)
					cache(op, result)
					lock.unlock()


				case ReadStrongField(GetFieldOp(path, fldName)) =>
					ReadResult(internalGetField(path, fldName))

				case _ => super.handleRequest(request)
			}
		}


		class StrongFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Strong]
		) extends StrongReplicatedObject[Addr, T] {
			setObject(init)


			protected override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {

				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq)
				setObject(masterObj)
				val res = super.internalInvoke[R](opid, methodName, args)
				handler.request(addr, MergeAndUnlock(getObject, InvokeOp(opid, methodName, args), res))
				handler.close()
				res
			}

			override protected def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)
				val ReadResult(res : R) = handler.request(addr, ReadStrongField(GetFieldOp(opid, fldName)))
				handler.close()
				res
			}

			override protected def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {

				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val LockRes(masterObj : T) = handler.request(addr, LockReq)
				setObject(masterObj)
				super.internalSetField(opid, fldName, newVal)

				val mergeReq = MergeAndUnlock(getObject, SetFieldOp(opid, fldName, newVal), ())
				handler.request(addr, mergeReq)
				handler.close()
			}

			override protected def internalSync() : Unit = {
				super.internalSync()
			}
		}
	}


	private sealed trait StrongReq extends Request
	private case object LockReq extends StrongReq with ReturnRequest
	private case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
	private case class MergeAndUnlock(obj : AnyRef, op : Operation[Any], result : Any) extends StrongReq with ReturnRequest
	private case class ReadStrongField(op : GetFieldOp[Any]) extends StrongReq with ReturnRequest



//	private case object SynchronizeWithStrongMaster extends StrongReq with ReturnRequest
//
//	private case class StrongSynchronized[T <: AnyRef](obj : T)
	private case class ReadResult(res : Any)



	private case object MergeAck

}
