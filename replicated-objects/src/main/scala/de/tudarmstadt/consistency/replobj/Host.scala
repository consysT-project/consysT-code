package de.tudarmstadt.consistency.replobj

import akka.actor.{Actor, ActorRef}

import scala.collection.mutable

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
class Host extends Actor {
	private val objDir : mutable.Map[Symbol, /*obj actors*/ ActorRef] = mutable.HashMap.empty

	private val otherHosts : mutable.Set[/*host actors*/ ActorRef] = mutable.Set.empty

	sealed trait HostMsg
	case class AddHost(ref : ActorRef) extends HostMsg
	case class AddObj(sym : Symbol, ref : ActorRef) extends HostMsg

	override def receive: Receive = {
		case AddHost(ref) =>
			otherHosts.add(ref)
	}





}
