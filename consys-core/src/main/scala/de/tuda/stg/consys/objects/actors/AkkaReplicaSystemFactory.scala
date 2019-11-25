package de.tuda.stg.consys.objects.actors

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.objects.{Address, ConsistencyLevel, ReplicaSystemFactory}

import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.util.Random

import scala.reflect.runtime.universe._


/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
object AkkaReplicaSystemFactory extends ReplicaSystemFactory {

	override type System = AkkaReplicaSystem { type Addr = String }

	private class AkkaReplicaSystemImpl(override val actorSystem : ActorSystem, override val defaultTimeout : FiniteDuration)
		extends AkkaReplicaSystem
			with StrongAkkaReplicaSystem
			with WeakAkkaReplicaSystem
			with CausalAkkaReplicaSystem
	{

		type Addr = String

		override protected def freshAddr() : String =
			"$" + String.valueOf(Random.alphanumeric.take(16).toArray)


		override type Ref[T <: AnyRef] = AkkaRef[String, T]

		override protected def newRef[T <: AnyRef : TypeTag](addr : String, consistencyLevel : ConsistencyLevel) : Ref[T] =
			new AkkaRef(addr, consistencyLevel, this)
	}


	override def create(host : Address, others : Seq[Address], timeout : Duration) : System = {
		require(timeout.isFinite())

		//Loads the reference.conf for the akka properties
		val config = ConfigFactory.load()
			.withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(host.hostname))
			.withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(host.port))
			.resolve()

		//Creates the actor system
		val system = ActorSystem(DEFAULT_ACTORSYSTEM_NAME, config)
		system.log.info(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

		//Creates and initializes the replica system
		val replicaSystem = new AkkaReplicaSystemImpl(system, timeout match {
			case x : FiniteDuration => x
			case x => FiniteDuration(x.toMillis, "ms")
		})
		others.foreach(address => {
			replicaSystem.addOtherReplica(address.hostname, address.port)
		})

		replicaSystem
	}




//	def create(actorSystem : ActorSystem, defaultTimeout : FiniteDuration) : AkkaReplicaSystem {type Addr = String} =
//		new AkkaReplicaSystemImpl(actorSystem, defaultTimeout)
//
//	def create(actorSystem : ActorSystem) : AkkaReplicaSystem {type Addr = String} =
//		create(actorSystem, Duration(60, "s"))
//
//	def create(port : Int, defaultTimeout : FiniteDuration) : AkkaReplicaSystem {type Addr = String} =
//		create("127.0.0.1", port, defaultTimeout)
//
//	def create(port : Int) : AkkaReplicaSystem {type Addr = String} =
//		create(port, Duration(60, "s"))
//
//	def create(hostname : String, port : Int) : AkkaReplicaSystem {type Addr = String} =
//		create(hostname, port, Duration(60, "s"))


}
