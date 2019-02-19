package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.Ref.LocalRef

import scala.reflect.runtime.universe._

/**
	* Created on 19.02.19.
	*
	* @author Mirko Köhler
	*/
class LocalObjectRef[T, L : TypeTag](ref : ActorRef) extends ObjectRef[T, L](ref) with LocalRef[T, L] {

	override def merge() : Unit = ???
}
