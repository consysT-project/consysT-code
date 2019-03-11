package de.tudarmstadt.consistency.replobj

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{Config, ConfigFactory}

/**
	* Created on 08.03.19.
	*
	* @author Mirko Köhler
	*/
package object actors {

	private[actors] final val DEFAULT_ACTORSYSTEM_NAME : String = "replica-system"

	private class AkkaReplicaSystemImpl[Addr](override val actorSystem: ActorSystem)
		extends AkkaReplicaSystem[Addr]
		with StrongAkkaReplicaSystem[Addr]
		with WeakAkkaReplicaSystem[Addr]

	def createReplicaSystem[Addr](actorSystem : ActorSystem) : AkkaReplicaSystem[Addr] =
		new AkkaReplicaSystemImpl[Addr](actorSystem)

	def createReplicaSystem[Addr](port : Int) : AkkaReplicaSystem[Addr] = {
		val config : Config = ConfigFactory.parseString(
			s"""
				 |akka {
				 | actor.provider = "remote"
				 | remote {
				 |   netty.tcp {
				 |     hostname = "127.0.0.1"
				 |     port = $port
				 |   }
				 | }
				 |}
			""".stripMargin)

		val system = ActorSystem(DEFAULT_ACTORSYSTEM_NAME, config)
		println(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")
		new AkkaReplicaSystemImpl[Addr](system)
	}

}
