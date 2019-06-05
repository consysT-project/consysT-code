package de.tuda.stg.consys.objects.crdt

import java.util.concurrent.TimeUnit

import akka.actor.{ActorSystem, Props}
import akka.util.Timeout
import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.objects.crdt.OpBasedCRDT.{RegisterAtReplica, RegisterReplica}

import scala.concurrent.ExecutionContext
import scala.concurrent.duration.Duration

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
object Main extends App {

	example2()

	def createSystem() : ActorSystem = {
		val hostname = "127.0.0.1"
		val port = 2553
		val config : Config = ConfigFactory.parseString(
			s"""
				 |akka {
				 | actor.provider = "remote"
				 | actor.warn-about-java-serializer-usage = false
				 | remote {
				 |   netty.tcp {
				 |     hostname = "$hostname"
				 |     port = $port
				 |   }
				 | }
				 | loglevel = WARNING
				 |}
				 |
				 |request-dispatcher {
				 |  executor = "thread-pool-executor"
				 |  type = PinnedDispatcher
				 |}
			""".stripMargin)


		ActorSystem("crdts", config)
	}

	def example1(): Unit = {
		import akka.pattern.ask
		import de.tuda.stg.consys.objects.crdt.CounterCRDT._

		val system1 = createSystem()

		val crdt1 = system1.actorOf(Props(classOf[CounterCRDT.StateBased]))
		val crdt2 = system1.actorOf(Props(classOf[CounterCRDT.StateBased]))

		crdt1 ! RegisterAtReplica(crdt2)
		crdt2 ! RegisterAtReplica(crdt1)

		Thread.sleep(1000)


		crdt1 ! Inc
		crdt1 ! Inc
		crdt2 ! Inc
		crdt2 ! Inc
		crdt1 ! Inc
		crdt2 ! Inc
		crdt1 ! Inc
		crdt1 ! Inc
		crdt2 ! Inc
		crdt2 ! Inc
		crdt1 ! Inc

		Thread.sleep(1000)

		implicit val timeOut = Timeout(Duration(10, TimeUnit.SECONDS))
		implicit val executionContext = ExecutionContext.global

		(crdt1 ? Get).foreach(println)
		(crdt2 ? Get).foreach(println)
	}


	def example2(): Unit = {
		import akka.pattern.ask
		import de.tuda.stg.consys.objects.crdt.AddOnlySetCRDT._


		val system1 = createSystem()

		val crdt1 = system1.actorOf(Props(classOf[AddOnlySetCRDT.StateBased[Int]]))
		val crdt2 = system1.actorOf(Props(classOf[AddOnlySetCRDT.StateBased[Int]]))

		crdt1 ! RegisterAtReplica(crdt2)
		crdt2 ! RegisterAtReplica(crdt1)

		Thread.sleep(1000)


		crdt1 ! Add(1)
		crdt1 ! Add(3)
		crdt2 ! Add(2)
		crdt2 ! Add(4)
		crdt1 ! Add(2)
		crdt2 ! Add(5)
		crdt1 ! Add(1)
		crdt1 ! Add(6)
		crdt2 ! Add(8)
		crdt2 ! Add(7)
		crdt1 ! Add(8)

		Thread.sleep(1000)

		implicit val timeOut = Timeout(Duration(10, TimeUnit.SECONDS))
		implicit val executionContext = ExecutionContext.global

		(crdt1 ? Contains(5)).foreach(println)
		(crdt2 ? Contains(5)).foreach(println)

		(crdt1 ? Contains(9)).foreach(println)
		(crdt2 ? Contains(9)).foreach(println)

		(crdt1 ? Get).foreach(println)
		(crdt2 ? Get).foreach(println)
	}




}
