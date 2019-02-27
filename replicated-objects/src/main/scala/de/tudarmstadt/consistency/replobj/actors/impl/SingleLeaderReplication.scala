package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.Replicable
import de.tudarmstadt.consistency.replobj.actors.impl.ObjectActor.Event
import de.tudarmstadt.consistency.replobj.actors.impl.SingleLeaderReplication.{Init, Replicate}

import scala.collection.mutable
import scala.concurrent.Await
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 15.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] trait SingleLeaderReplication {


	protected trait LeaderActor[T <: AnyRef, L] extends ObjectActor[T, L] {

		protected val followers : mutable.Set[ActorRef] = mutable.HashSet.empty

		override def receiveEvent : PartialFunction[Event, Unit] = {
			/*distributed operations*/
			case Replicate(follower, ctt) =>
				//Dynamically check that replicas have the correct consistency level
				if (ctt != consistencyTag) sys.error(s"incompatible consistency level of replica. expected $consistencyTag, but got $ctt")

				//Returns: an actor with the current replicated state of this actor
				followers += follower
				sender() ! obj

			case evt => super.receiveEvent(evt)
		}
	}


	protected trait FollowerActor[T <: AnyRef, L] extends ObjectActor[T, L] {

		protected val leader : ActorRef

		override def receiveEvent : PartialFunction[Event, Unit] = {
			case Init =>
				import akka.pattern.ask
				import scala.concurrent.duration._

				implicit val timeout : Timeout = Timeout(5 seconds)

				val response = leader ? Replicate(self, consistencyTag)
				val state : T = Await.result(response, 5 seconds).asInstanceOf[T]

				state match {
					case s : Replicable => s.replicated()
				}

				obj = state

			case evt => super.receiveEvent(evt)
		}
	}
}

object SingleLeaderReplication {

	case object Init extends Event
	case class Replicate[L](follower : ActorRef, consistencyLevel : TypeTag[L]) extends Event
}
