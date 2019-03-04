package de.tudarmstadt.consistency.demo

import akka.actor.ActorSystem
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak
import de.tudarmstadt.consistency.replobj.ReplicaSystem
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	val replica : ReplicaSystem[String] = AkkaReplicaSystem.create[String](3773)

	val ref  = replica.replicate[A, Weak]("a", A(3))

	ref("i") = 55
	println(ref("i"))

}

case class A(i : Int)