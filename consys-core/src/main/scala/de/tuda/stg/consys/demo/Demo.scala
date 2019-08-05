package de.tuda.stg.consys.demo

import de.tuda.stg.consys.objects.ConsistencyLevel.{High, Low, Strong, Weak}
import de.tuda.stg.consys.objects.actors
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	case class A(var i : Int) {
		@deprecated def inc() : Unit = i = i + 1
		def inc(a : Int) : Unit = i = i + a
	}

	val replica1 : AkkaReplicaSystem[String] = actors.createReplicaSystem[String](3773)
	val replica2 : AkkaReplicaSystem[String] = actors.createReplicaSystem[String](3774)

	try {
		replica1.addOtherReplica("127.0.0.1", 3774)
		replica2.addOtherReplica("127.0.0.1", 3773)

		Thread.sleep(1000)

		val ref1 = replica1.replicate("a", A(3), High)
		val ref2 = replica2.lookup[A]("a", High)

		Thread.sleep(1000)

		replica2.delete("a")

		replica1.replicate("a", A(4234), High)

		ref2("i") = 55

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

		ref2.sync()

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

		ref1 <= ("inc", 3)

		ref2.sync()

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}")

		Thread.sleep(1000)
	} finally {


		replica1.close()
		replica2.close()
	}


}

