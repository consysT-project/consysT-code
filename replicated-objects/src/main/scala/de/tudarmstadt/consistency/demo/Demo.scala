package de.tudarmstadt.consistency.demo

import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Strong
import de.tudarmstadt.consistency.replobj.actors
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem

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

	val ref1  = replica1.replicate("a", A(3), Strong)
	val ref2 = replica2.ref[A]("a", Strong)

	Thread.sleep(1000)


	ref2("i") = 55
	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

	ref2.sync()

	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")



}

case class A(i : Int)