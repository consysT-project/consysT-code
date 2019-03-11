package de.tudarmstadt.consistency.demo

import de.tudarmstadt.consistency.replobj.ConsistencyLevels.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.{ReplicaSystem, actors}

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	val replica : ReplicaSystem[String] = actors.createReplicaSystem[String](3773)

	val ref  = replica.replicate[A, Weak]("a", A(3))

	ref("i") = 55
	println(ref("i"))

}

case class A(i : Int)