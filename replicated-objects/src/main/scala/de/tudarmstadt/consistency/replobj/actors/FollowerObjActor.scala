package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.ObjActor.{Init, Replicate, Replicated}

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
private[actors] class FollowerObjActor[T <: AnyRef](private val master : ActorRef, tt : TypeTag[T]) extends ObjActor[T](null.asInstanceOf[T], tt) {


	override def receive : Receive = {
		case Init =>
			import akka.pattern.ask

			implicit val timeout : Timeout = Timeout(5 seconds)

			val response = master ? Replicate

			val state = Await.result(response, 5 seconds)
			obj = state.asInstanceOf[T]

		case msg => super.receive(msg)
	}


}



