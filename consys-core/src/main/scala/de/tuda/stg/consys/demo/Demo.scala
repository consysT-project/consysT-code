package de.tuda.stg.consys.demo

import de.tuda.stg.consys.objects.ConsistencyLevel.{Cassandra, High, Low, Strong, Weak}
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
	val replica3 : AkkaReplicaSystem[String] = actors.createReplicaSystem[String](3775)


	try {
		replica1.addOtherReplica("127.0.0.1", 3774)
		replica1.addOtherReplica("127.0.0.1", 3775)

		replica2.addOtherReplica("127.0.0.1", 3773)
		replica2.addOtherReplica("127.0.0.1", 3775)

		replica3.addOtherReplica("127.0.0.1", 3773)
		replica3.addOtherReplica("127.0.0.1", 3774)

		Thread.sleep(1000)

		val ref1 = replica1.replicate("a", A(3), Cassandra(2))
		val ref2 = replica2.lookup[A]("a", Cassandra(2))
		val ref3 = replica3.lookup[A]("a", Cassandra(2))


		ref2("i") = 55

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}, ref3.i = ${ref3("i")}")

//		ref2.sync()

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}, ref3.i = ${ref3("i")}")

//		ref1 <= ("inc", 3)
//
//		ref2.sync()

		println(s"ref1.i = ${ref1("i")}, ref2.i = ${ref2("i")}, ref3.i = ${ref3("i")}")

		Thread.sleep(1000)
	} finally {


		replica1.close()
		replica2.close()
	}


}

