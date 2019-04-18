package de.tuda.stg.consys.demo

import de.tuda.stg.consys.objects.ConsistencyLevel.{Strong, Weak}
import de.tuda.stg.consys.objects.actors
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem

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

	val ref1  = replica1.replicate("a", A(3), Weak)
	val ref2 = replica2.ref[A]("a", Weak)

	Thread.sleep(1000)


	ref2("i") = 55

	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

	ref2.sync()

	println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")


	replica1.close()
	replica2.close()

}

case class A(i : Int)