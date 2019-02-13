package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, Props}
import de.tudarmstadt.consistency.replobj.actors.ObjActor.{Replicate, Replicated}

import scala.collection.mutable
import scala.reflect.runtime.universe._

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] class MasterObjActor[T <: AnyRef](oo : T, tt : TypeTag[T]) extends ObjActor(oo, tt) {

	private val followers : mutable.Set[ActorRef] = mutable.HashSet.empty


	override def receive : Receive = {

		/*distributed operations*/
		case Replicate =>
			//Returns: an actor with the current replicated state of this actor
			followers += sender()
			println("followers: " + followers)
			sender() ! obj

		case msg => super.receive(msg)

	}


}



