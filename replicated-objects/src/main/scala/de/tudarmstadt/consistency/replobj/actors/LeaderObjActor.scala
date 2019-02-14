package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, Props}
import de.tudarmstadt.consistency.replobj.actors.ObjActor.{Replicate, SetObj}

import scala.collection.mutable
import scala.reflect.runtime.universe._

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] trait LeaderObjActor[T <: AnyRef, L] extends ObjActor[T, L] {

	protected val followers : mutable.Set[ActorRef] = mutable.HashSet.empty


	override def receive : Receive = {

		/*distributed operations*/
		case Replicate(follower, ctt) =>
			//Dynamically check that replicas have the correct consistency level
			if (ctt != consistencytag) sys.error(s"incompatible consistency level of replica. expected $consistencytag, but got $ctt")

			//Returns: an actor with the current replicated state of this actor
			followers += follower
			sender() ! obj

		case msg => super.receive(msg)

	}


}



