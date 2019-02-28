package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak

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
abstract class WeakAkkaReplicatedObject[Addr, T : TypeTag] extends AkkaReplicatedObject[T, Weak]


object WeakAkkaReplicatedObject {

	class WeakAkkaMasterReplicatedObject[Addr, T : TypeTag](obj : T, actorSystem : ActorSystem) extends WeakAkkaReplicatedObject[Addr, T] {

		override val objActor : ActorRef =
			actorSystem.actorOf(Props(classOf[MasterActor], this, obj, typeTag[T]))


		override def synchronize() : Unit =
			throw new UnsupportedOperationException("synchronize on master")


		class MasterActor(protected var obj : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {

			override def receive : Receive = {
				case MethodInv(mthdName, args) =>
					val res = invoke[Any](mthdName, args : _*)
					sender() ! res

				case FieldGet(fldName) => //No coordination needed in the get case
					val res = getField[Any](fldName)
					sender() ! res

				case FieldSet(fldName, value) =>
					setField[Any](fldName, value)

				case SynchronizeReq(events) =>
					events.foreach(e => applyEvent(e))
					sender() ! SynchronizeRes(obj)

				case msg => super.receive(msg)
			}
		}
	}


	class WeakAkkaFollowerReplicatedObject[Addr, T : TypeTag](obj : T, masterRef : ActorRef, actorSystem : ActorSystem) extends WeakAkkaReplicatedObject[Addr, T] {

		override val objActor : ActorRef =
			actorSystem.actorOf(Props(classOf[FollowerActor], this, obj, typeTag[T]))


		override def synchronize() : Unit = {
			objActor ! Synchronize
		}



		class FollowerActor(protected var obj : T, protected implicit val objtag : TypeTag[T]) extends ObjectActor {

			/*stores the operations since last synchronize*/
			val unsynchronized : mutable.Buffer[Event[_]] = mutable.Buffer.empty


			override def receive : Receive = {
				case MethodInv(mthdName, args) =>
					unsynchronized += InvokeOp(mthdName, args)
					val res = invoke[Any](mthdName, args : _*)
					sender() ! res

				case FieldGet(fldName) => //No coordination needed in the get case
					val res = getField[Any](fldName)
					sender() ! res

				case FieldSet(fldName, value) =>
					unsynchronized += SetFieldOp(fldName, value)
					setField[Any](fldName, value)

				case Synchronize =>
					import akka.pattern.ask

					//TODO: Also synchronize operations from other related objects?

					implicit val timeout : Timeout = Timeout(5 seconds)
					val response = masterRef ? SynchronizeReq(unsynchronized)

					val SynchronizeRes(newObj) = Await.result(response, 5 seconds)

					obj = newObj.asInstanceOf[T]
					unsynchronized.clear()

				case msg => super.receive(msg)
			}
		}
	}
}
