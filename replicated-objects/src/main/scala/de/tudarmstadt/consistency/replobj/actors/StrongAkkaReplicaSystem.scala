package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, Props}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Strong
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._
import de.tudarmstadt.consistency.replobj.actors.StrongAkkaReplicaSystem.StrongReplicatedObject.{StrongFollowerReplicatedObject, StrongMasterReplicatedObject}

import scala.collection.mutable
import scala.concurrent.duration._
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

	trait StrongReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T, Strong] with AkkaMultiversionReplicatedObject[Addr, T, Strong]


	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Strong]
		) extends StrongReplicatedObject[Addr, T] {

			override val objActor : ActorRef =
				replicaSystem.actorSystem.actorOf(Props(classOf[ActorImpl], this, init, typeTag[T]))


			private class ActorImpl(init : T, protected implicit val objtag : TypeTag[T])
				extends ObjectActor
				with MultiversionObjectActor {
				setObject(init)

				private val lockQueue : mutable.Queue[(ActorRef, Request)] = mutable.Queue.empty

				override def receive : Receive = {
					case OpReq(InvokeOp(id, mthdName, args)) =>
						val res = internalInvoke[Any](id, mthdName, args : _*)
						sender() ! res

					case OpReq(GetFieldOp(id, fldName)) => //No coordination needed in the get case
						val res = internalGetField[Any](id, fldName)
						sender() ! res

					case OpReq(SetFieldOp(id, fldName, value)) =>
						internalSetField(id, fldName, value)
						sender() ! SetFieldAck

					case SyncReq =>
						throw new UnsupportedOperationException("cannot synchronize strong consistent object: already synchronized")

					case SynchronizeWithStrongMaster =>
						sender() ! StrongSynchronized(getObject)

					case LockReq =>
						context.become {
							case msg@OpReq(InvokeOp(_, _, _)) =>
								lockQueue.enqueue((sender(), msg))

							case msg@OpReq(SetFieldOp(_, _, _)) =>
								lockQueue.enqueue((sender(), msg))

							case msg@LockReq =>
								lockQueue.enqueue((sender(), msg))


							case MergeAndUnlock(newObj : T) =>
								setObject(newObj)
								sender() ! MergeAck

								context.unbecome()

								while (lockQueue.nonEmpty) {
									val (senderRef, message) = lockQueue.dequeue()
									self.tell(message, senderRef)
								}


							case OpReq(GetFieldOp(id, fldName)) =>
								//No coordination needed in the get case
								//Lock does not prevent get from happening
								val res = internalGetField[Any](id, fldName)
								sender() ! res

							case SynchronizeWithStrongMaster =>
								//Synchronization still works even if the object is locked
								sender() ! StrongSynchronized(getObject)
						}
						sender() ! LockRes(getObject)
				}
			}

		}

		class StrongFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Strong]
		) extends StrongReplicatedObject[Addr, T] {

			override val objActor : ActorRef =
				replicaSystem.actorSystem.actorOf(Props(classOf[ActorImpl], this, init, typeTag[T]))


			private class ActorImpl(init : T, protected implicit val objtag : TypeTag[T])
				extends ObjectActor
				with MultiversionObjectActor {
				setObject(init)

				override def receive : Receive = {

					case OpReq(InvokeOp(id, mthdName, args)) =>
						val LockRes(masterObj : T) = replicaSystem.request(addr, LockReq, masterReplica, receiveTimeout = 60 seconds)
						setObject(masterObj)
						val res = internalInvoke[Any](id, mthdName, args : _*)
						replicaSystem.request(addr, MergeAndUnlock(getObject), masterReplica)
						sender() ! res

					case OpReq(GetFieldOp(id, fldName)) =>
						val StrongSynchronized(newObj : T) = replicaSystem.request(addr, SynchronizeWithStrongMaster, masterReplica)
						setObject(newObj)
						sender() ! internalGetField[Any](id, fldName)


					case OpReq(SetFieldOp(id, fldName, value)) =>
						val LockRes(masterObj : T) = replicaSystem.request(addr, LockReq, masterReplica, receiveTimeout = 60 seconds)
						setObject(masterObj)
						internalSetField(id, fldName, value)
						replicaSystem.request(addr, MergeAndUnlock(getObject), masterReplica)
						sender() ! SetFieldAck

					case SyncReq =>
						throw new UnsupportedOperationException("cannot synchronize strong consistent object: already synchronized")
				}

			}
		}
	}


	private sealed trait StrongReq extends Request
	private case object LockReq extends StrongReq with ReturnRequest
	private case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
	private case class MergeAndUnlock(obj : AnyRef) extends StrongReq with ReturnRequest
	private case object SynchronizeWithStrongMaster extends StrongReq with ReturnRequest

	private case class StrongSynchronized[T <: AnyRef](obj : T)


	private case object MergeAck

}
