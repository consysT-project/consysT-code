package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] class AvailableFollowerActor[T](m : ActorRef, tt : TypeTag[T]) extends FollowerObjActor[T](m, tt) {

}
