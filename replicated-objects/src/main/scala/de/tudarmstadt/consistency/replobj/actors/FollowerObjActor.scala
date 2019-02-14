package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.ObjActor.{Init, Replicate, SetObj}

import scala.collection.mutable
import scala.concurrent.Await
import scala.reflect.runtime.universe._
import scala.concurrent.duration._
import scala.language.postfixOps

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] trait FollowerObjActor[T <: AnyRef, L] extends ObjActor[T, L] {

	protected val leader : ActorRef

	override def receive : Receive = {
		case Init =>
			import akka.pattern.ask

			implicit val timeout : Timeout = Timeout(5 seconds)

			val response = leader ? Replicate(self, consistencytag)

			val state = Await.result(response, 5 seconds)
			obj = state.asInstanceOf[T]

		case msg => super.receive(msg)
	}


}



