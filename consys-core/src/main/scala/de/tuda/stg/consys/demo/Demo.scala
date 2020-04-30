package de.tuda.stg.consys.demo

import java.util.concurrent.{Executors, TimeUnit}

import akka.dispatch.ExecutionContexts
import de.tuda.stg.consys.core.ConsistencyLabel.Strong
import de.tuda.stg.consys.core.akka.{AkkaReplicaSystemFactory, AkkaReplicaSystems}

import scala.concurrent.ExecutionContext

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

	val service = Executors.newFixedThreadPool(12)
	implicit val executionContext : ExecutionContext = ExecutionContexts.fromExecutorService(service)

	AkkaReplicaSystems.spawn("test/consys0.conf") {
		import AkkaReplicaSystems.{system => sys}

		val ref = sys.replicate("a", A(3), Strong)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}


	AkkaReplicaSystems.spawn("test/consys1.conf") {
		import AkkaReplicaSystems.{system => sys}

		val ref = sys.lookup[A]("a", Strong)
		println(s"ref.i = ${ref("i")}")
		ref("i") = 55
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}

	AkkaReplicaSystems.spawn("test/consys2.conf") {
		import AkkaReplicaSystems.{system => sys}

		val ref = sys.lookup[A]("a", Strong)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(500)
		println(s"ref.i = ${ref("i")}")
		Thread.sleep(5000)
	}

	service.awaitTermination(10, TimeUnit.SECONDS)


}

