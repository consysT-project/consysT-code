package de.tuda.stg.consys.demo

import java.util.concurrent.Executors

import akka.dispatch.ExecutionContexts
import de.tuda.stg.consys.objects.ConsistencyLevel.{Cassandra, High, Low, Strong, Weak}
import de.tuda.stg.consys.objects.actors
import de.tuda.stg.consys.objects.actors.{AkkaReplicaSystem, AkkaReplicaSystemFactory}

import scala.concurrent.{ExecutionContext, ExecutionContextExecutorService}

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

	implicit val executionContext : ExecutionContext = ExecutionContexts.fromExecutorService(Executors.newFixedThreadPool(12))


	AkkaReplicaSystemFactory.spawn("test/consys0.conf") { system =>
		import system.println

		val ref = system.replicate("a", A(3), Strong)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}


	AkkaReplicaSystemFactory.spawn("test/consys1.conf") { system =>
		import system.println

		val ref = system.lookup[A]("a", Strong)
		println(s"ref.i = ${ref("i")}")
		ref("i") = 55
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}

	AkkaReplicaSystemFactory.spawn("test/consys2.conf") { system =>
		import system.println

		val ref = system.lookup[A]("a", Strong)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}

}

