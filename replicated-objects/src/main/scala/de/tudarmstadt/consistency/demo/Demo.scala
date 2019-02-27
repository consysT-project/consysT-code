package de.tudarmstadt.consistency.demo

import akka.actor.ActorSystem
import de.tudarmstadt.consistency.replobj.ConsistencyLevels
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	val system = ActorSystem.create("demo")

	val replica = new AkkaReplicaSystem[String] {
		override def actorSystem : ActorSystem = system
		override def name : String = "replica1"
	}


	replica.replicate[A, ConsistencyLevels.Weak]("a", A(3))



}

case class A(i : Int)