package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, Props}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Strong
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem.{Request, ReturnRequest}
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

	trait StrongReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T, Strong]


	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Strong]
		) extends StrongReplicatedObject[Addr, T] {

			override val objActor : ActorRef =
				replicaSystem.actorSystem.actorOf(Props(classOf[ObjectActorImpl], this, init, typeTag[T]))

			private class ObjectActorImpl(init : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {
				setObject(init)

				private val lockQueue : mutable.Queue[(ActorRef, Any)] = mutable.Queue.empty

				override def receive : Receive = {
					case InvokeReq(mthdName, args) =>
						val res = ReflectiveAccess.doInvoke[Any](mthdName, args : _*)
						sender() ! res

					case GetFieldReq(fldName) => //No coordination needed in the get case
						val res = ReflectiveAccess.doGetField[Any](fldName)
						sender() ! res

					case SetFieldReq(fldName, value) =>
						ReflectiveAccess.doSetField[Any](fldName, value)
						sender() ! Unit

					case SyncReq =>
						throw new UnsupportedOperationException("cannot synchronize strong consistent object: already synchronized")

					case LockReq =>
						context.become {
							case msg@InvokeReq(mthdName, args) =>
								lockQueue.enqueue((sender(), msg))

							case msg@GetFieldReq(fldName) => //No coordination needed in the get case
								lockQueue.enqueue((sender(), msg))

							case msg@SetFieldReq(fldName, value) =>
								lockQueue.enqueue((sender(), msg))

							case msg@LockReq =>
								lockQueue.enqueue((sender(), msg))

							case MergeAndUnlock(newObj : T) =>
								setObject(newObj)
								sender() ! "ack"

								context.unbecome()

								while (lockQueue.nonEmpty) {
									val (senderRef, message) = lockQueue.dequeue()
									self.tell(message, senderRef)
								}
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
				replicaSystem.actorSystem.actorOf(Props(classOf[ObjectActorImpl], this, init, typeTag[T]))


			private class ObjectActorImpl(init : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {
				setObject(init)

				override def receive : Receive = {

					case InvokeReq(mthdName, args) =>
						val LockRes(masterObj : T) = replicaSystem.request(addr, LockReq, masterReplica, receiveTimeout = 60 seconds)
						setObject(masterObj)
						val res = ReflectiveAccess.doInvoke(mthdName, args : _*)
						replicaSystem.request(addr, MergeAndUnlock(getObject), masterReplica)
						sender() ! res

					case GetFieldReq(fldName) =>
						sender() ! replicaSystem.request(addr, GetFieldReq(fldName), masterReplica)


					case SetFieldReq(fldName, value) =>
						val LockRes(masterObj : T) = replicaSystem.request(addr, LockReq, masterReplica, receiveTimeout = 60 seconds)
						setObject(masterObj)
						ReflectiveAccess.doSetField(fldName, value)
						replicaSystem.request(addr, MergeAndUnlock(getObject), masterReplica)
						sender() ! Unit

					case SyncReq =>
						throw new UnsupportedOperationException("cannot synchronize strong consistent object: already synchronized")
				}

			}
		}


		private sealed trait StrongReq extends Request
		private case object LockReq extends StrongReq with ReturnRequest
		private case class LockRes(obj : AnyRef) extends StrongReq with ReturnRequest
		private case class MergeAndUnlock(obj : AnyRef) extends StrongReq with ReturnRequest

	}

}
