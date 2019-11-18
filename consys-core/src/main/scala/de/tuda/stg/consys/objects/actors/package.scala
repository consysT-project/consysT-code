package de.tuda.stg.consys.objects

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{Config, ConfigFactory, ConfigResolveOptions, ConfigValue, ConfigValueFactory}

import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.util.Random
import scala.reflect.runtime.universe._


/**
	* Created on 08.03.19.
	*
	* @author Mirko Köhler
	*/
package object actors {

	private[actors] final val DEFAULT_ACTORSYSTEM_NAME : String = "replica-system"

	private class AkkaReplicaSystemImpl(override val actorSystem: ActorSystem, override val defaultTimeout : FiniteDuration)
		extends AkkaReplicaSystem[String]
		with StrongAkkaReplicaSystem[String]
		with WeakAkkaReplicaSystem[String]
//		with HighAkkaReplicaSystem[String]
//		with LowAkkaReplicaSystem[String]
//		with CassandraAkkaReplicaSystem[String]
	{

		override protected def freshAddr() : String =
			"$" + String.valueOf(Random.alphanumeric.take(16).toArray)


		override type Ref[T <: AnyRef] = AkkaRef[String, T]

		override protected def newRef[T <: AnyRef : TypeTag](addr : String, consistencyLevel : ConsistencyLevel) : Ref[T] =
			new AkkaRef(addr, consistencyLevel, this)
	}

	def createReplicaSystem(actorSystem : ActorSystem, defaultTimeout : FiniteDuration) : AkkaReplicaSystem[String] =
		new AkkaReplicaSystemImpl(actorSystem, defaultTimeout)

	def createReplicaSystem(actorSystem : ActorSystem) : AkkaReplicaSystem[String] =
		createReplicaSystem(actorSystem, Duration(60, "s"))

	def createReplicaSystem[Addr](port : Int, defaultTimeout : FiniteDuration) : AkkaReplicaSystem[String] =
		createReplicaSystem("127.0.0.1", port, defaultTimeout)

	def createReplicaSystem[Addr](port : Int) : AkkaReplicaSystem[String] =
		createReplicaSystem(port, Duration(60, "s"))

	def createReplicaSystem[Addr](hostname : String, port : Int) : AkkaReplicaSystem[String] =
		createReplicaSystem(hostname, port, Duration(60, "s"))

	def createReplicaSystem[Addr](hostname : String, port : Int, defaultTimeout : FiniteDuration) : AkkaReplicaSystem[String] = {
		/*
		val config : Config = ConfigFactory.parseString(
			s"""
				 |akka {
				 |  actor {
				 |    provider = remote
				 |    warn-about-java-serializer-usage = false
				 |  }
				 |  loglevel = WARNING
				 |}
				 |
				 |request-dispatcher {
				 |  executor = "thread-pool-executor"
				 |  type = PinnedDispatcher
				 |}
			""".stripMargin)
		 */

		val config = ConfigFactory.load()
//  		.withFallback(ConfigFactory.defaultApplication())
			.withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(hostname))
			.withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(port))
			.resolve()

		val system = ActorSystem(DEFAULT_ACTORSYSTEM_NAME, config)
		system.log.info(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")
		createReplicaSystem(system, defaultTimeout)
	}

}
