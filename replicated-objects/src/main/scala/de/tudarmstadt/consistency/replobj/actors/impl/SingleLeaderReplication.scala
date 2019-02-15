package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.impl.ObjActor.Message
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


	protected trait LeaderActor[T <: AnyRef, L] extends ObjActor[T, L] {

		protected val followers : mutable.Set[ActorRef] = mutable.HashSet.empty

		override def receive : Receive = {
			/*distributed operations*/
			case Replicate(follower, ctt) =>
				//Dynamically check that replicas have the correct consistency level
				if (ctt != consistencyTag) sys.error(s"incompatible consistency level of replica. expected $consistencyTag, but got $ctt")

				//Returns: an actor with the current replicated state of this actor
				followers += follower
				sender() ! obj

			case msg => super.receive(msg)
		}
	}


	protected trait FollowerActor[T <: AnyRef, L] extends ObjActor[T, L] {

		protected val leader : ActorRef

		override def receive : Receive = {
			case Init =>
				import akka.pattern.ask
				import scala.concurrent.duration._

				implicit val timeout : Timeout = Timeout(5 seconds)

				val response = leader ? Replicate(self, consistencyTag)

				val state = Await.result(response, 5 seconds)
				obj = state.asInstanceOf[T]

			case msg => super.receive(msg)
		}
	}
}

object SingleLeaderReplication {

	sealed trait CoordinationMessage extends Message
	case object Init extends CoordinationMessage
	case class Replicate[L](follower : ActorRef, consistencyLevel : TypeTag[L]) extends CoordinationMessage


}
