package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Strong
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
abstract class StrongAkkaReplicatedObject[T <: AnyRef : TypeTag] extends AkkaReplicatedObject[T, Strong]

object StrongAkkaReplicatedObject {

	class StrongAkkaMasterReplicatedObject[T <: AnyRef : TypeTag](obj : T/*creates actor in constructor*/, val replicaSystem : ActorReplicaSystem[_]) extends StrongAkkaReplicatedObject[T] {

		override val objActor : ActorRef =
			replicaSystem.actorSystem.actorOf(Props(classOf[MasterActor], this, obj, typeTag[T]))


		override def sync() : Unit =
			throw new UnsupportedOperationException("synchronize on strong consistent object")


		class MasterActor(protected var obj : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {

			private case class OpTag(opid : Int, seq : Int, parent : Option[Int] = None)

			private val opCache : mutable.Map[OpTag, Any] = mutable.Map.empty


			private val lockQueue : mutable.Queue[(ActorRef, Any)] = mutable.Queue.empty

			override def receive : Receive = {
				case MethodInv(mthdName, args) =>
					val res = invoke[Any](mthdName, args : _*)
					sender() ! res

				case FieldGet(fldName) => //No coordination needed in the get case
					val res = getField[Any](fldName)
					sender() ! res

				case FieldSet(fldName, value) =>
					setField[Any](fldName, value)
					sender() ! SetAck

				case LockReq =>
					context.become {
						case msg@MethodInv(mthdName, args) =>
							lockQueue.enqueue((sender(), msg))

						case msg@FieldGet(fldName) => //No coordination needed in the get case
							lockQueue.enqueue((sender(), msg))

						case msg@FieldSet(fldName, value) =>
							lockQueue.enqueue((sender(), msg))

						case msg@LockReq =>
							lockQueue.enqueue((sender(), msg))

						case msg@SynchronizeReq =>
							lockQueue.enqueue((sender(), msg))

						case MergeAndUnlock(newObj : T) =>
							setObject(newObj)
							sender() ! Ack

							context.unbecome()

							while (lockQueue.nonEmpty) {
								val (senderRef, message) = lockQueue.dequeue()
								self.tell(message, senderRef)
							}
					}

					sender() ! LockRes

				case SynchronizeReq =>
					sender() ! SynchronizeRes(obj)


				case msg => super.receive(msg)
			}
		}
	}

	class StrongAkkaFollowerReplicatedObject[T <: AnyRef : TypeTag](obj : T, masterRef : ActorRef, val replicaSystem : ActorReplicaSystem[_]) extends StrongAkkaReplicatedObject[T] {

		override val objActor : ActorRef =
			replicaSystem.actorSystem.actorOf(Props(classOf[FollowerActor], this, obj, typeTag[T]))


		override def sync() : Unit =
			throw new UnsupportedOperationException("synchronize on strong consistent object")




		class FollowerActor(protected var obj : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {

			override def receive : Receive = {

				case MethodInv(mthdName, args) =>
					val res = applyMutatingEvent(InvokeOp(mthdName, args))
					sender() ! res


				case FieldGet(fldName) => //No coordination needed in the get case
					import akka.pattern.ask
					val synchronizeResponse = masterRef.?(SynchronizeReq)(Timeout(10 seconds))
					val synchronize = Await.result(synchronizeResponse, 10 seconds)

					synchronize match {
						case SynchronizeRes(newObj : T) =>
							setObject(newObj)
							val fv = getField[Any](fldName)
							sender() ! fv
						case x => sys.error(s"unexpected message. expected SynchronizeRes, but got $x")
					}


				case FieldSet(fldName, value) =>
					applyMutatingEvent(SetFieldOp(fldName, value))
					sender() ! SetAck


				case msg => super.receive(msg)
			}


			private def applyMutatingEvent(op : Event[_]) : Any = {
				import akka.pattern.ask
				val lockResponse = masterRef.ask(LockReq)(Timeout(60 seconds))
				Await.ready(lockResponse, 60 seconds)




				val res = applyEvent(op)

				val mergeResponse = masterRef.ask(MergeAndUnlock(obj))(Timeout(10 seconds))
				Await.ready(mergeResponse, 10 seconds)

				res
			}
		}
	}



	private sealed trait Internal
	private case object LockReq extends Internal
	private case object LockRes extends Internal
	private case class MergeAndUnlock(obj : AnyRef) extends Internal
	private case object Ack extends Internal
	private case object SynchronizeReq extends Internal
	private case class SynchronizeRes(obj : AnyRef) extends Internal




}
