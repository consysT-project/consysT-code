package de.tudarmstadt.consistency.demo

import de.tudarmstadt.consistency.replobj.ConsistencyLevels.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem
import de.tudarmstadt.consistency.replobj.{ReplicaSystem, actors}

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	val replica1 : AkkaReplicaSystem[String] = actors.createReplicaSystem[String](3773)
	val replica2 : AkkaReplicaSystem[String] = actors.createReplicaSystem[String](3774)

	replica1.addOtherReplica("127.0.0.1", 3774)
	replica2.addOtherReplica("127.0.0.1", 3773)

	Thread.sleep(1000)

	val ref1  = replica1.replicate[A, Strong]("a", A(3))
	val ref2 = replica2.ref[A, Strong]("a")

	Thread.sleep(1000)

	ref2("i") = 55
	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

	ref2.sync()

	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")



}

case class A(i : Int)