package de.tuda.multijvm.test

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.cluster.Cluster

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps


/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
object DemoMultiJvmNode1 {
	def main(args: Array[String]) {
		println("Hello from node 1")

		val system = ActorSystem.create("test", config)
		val cluster = Cluster(system)


		val actorRef = system.actorOf(Props(classOf[DemoActor]), "act1")
		actorRef ! 11


		println(actorRef)

		val futureRef2 = system.actorSelection("/user/act1/").resolveOne(5 seconds)
		val ref2 : ActorRef = Await.result(futureRef2, 5 seconds)
		ref2 ! 22


		Thread.sleep(10000)
		system.terminate()
		sys.exit()

	}
}

object DemoMultiJvmNode2 {
	def main(args: Array[String]) {
		println("Hello from node 2")

		val system = ActorSystem.create("test", config)
		val cluster = Cluster(system)

//		implicit val executionContext : ExecutionContext =
//			ExecutionContexts.fromExecutorService(Executors.newFixedThreadPool(4))




		Thread.sleep(10000)
		system.terminate()
		sys.exit()

	}
}

//object DemoMultiJvmNode3 {
//	def main(args: Array[String]) {
//		println("Hello from node 3")
//
//		val system = ActorSystem.create("test")
//
//		Thread.sleep(5000)
//		system.terminate()
//	}
//}

