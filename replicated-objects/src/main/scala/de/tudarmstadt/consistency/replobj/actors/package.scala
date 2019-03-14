package de.tudarmstadt.consistency.replobj

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{Config, ConfigFactory}

import scala.util.Random

/**
	* Created on 08.03.19.
	*
	* @author Mirko Köhler
	*/
package object actors {

	private[actors] final val DEFAULT_ACTORSYSTEM_NAME : String = "replica-system"

	private class AkkaReplicaSystemImpl(override val actorSystem: ActorSystem)
		extends AkkaReplicaSystem[String]
		with StrongAkkaReplicaSystem[String]
		with WeakAkkaReplicaSystem[String] {

		override protected def freshAddr() : String =
			"$$" + String.valueOf(Random.alphanumeric.take(12).toArray)

	}

	def createReplicaSystem(actorSystem : ActorSystem) : AkkaReplicaSystem[String] =
		new AkkaReplicaSystemImpl(actorSystem)

	def createReplicaSystem[Addr](port : Int) : AkkaReplicaSystem[String] = {
		val config : Config = ConfigFactory.parseString(
			s"""
				 |akka {
				 | actor.provider = "remote"
				 | actor.warn-about-java-serializer-usage = false
				 | remote {
				 |   netty.tcp {
				 |     hostname = "127.0.0.1"
				 |     port = $port
				 |   }
				 | }
				 |}
				 |
				 |request-dispatcher {
				 |  executor = "thread-pool-executor"
				 |  type = PinnedDispatcher
				 |}
			""".stripMargin)

		val system = ActorSystem(DEFAULT_ACTORSYSTEM_NAME, config)
		println(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")
		new AkkaReplicaSystemImpl(system)
	}

}
