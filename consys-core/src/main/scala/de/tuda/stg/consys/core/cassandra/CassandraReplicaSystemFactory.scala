package de.tuda.stg.consys.core.cassandra

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.datastax.oss.driver.api.core.CqlSession
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.{Address, ConsistencyLevel, ReplicaSystemFactory}
import de.tuda.stg.consys.experimental.lang.LangBinding

import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.reflect.runtime.universe._
import scala.util.Random


/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
object CassandraReplicaSystemFactory extends ReplicaSystemFactory {

	override type System = CassandraReplicaSystem { type Addr = String; type Obj = LangBinding.Obj}

	private class CassandraReplicaSystemImpl(
		override val cqlSession : CqlSession,
		override val defaultTimeout : FiniteDuration
	) extends CassandraReplicaSystem {
		override type Obj = LangBinding.Obj
		override protected def freshAddr : String = ""
	2}

	def create() : System = new CassandraReplicaSystemImpl(CqlSession.builder.build, Duration(60, "s"))

	override def create(host : Address, others : Seq[Address], timeout : Duration) : System = {
		require(timeout.isFinite())
		create()
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
