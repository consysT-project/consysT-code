package de.tuda.stg.consys.core.legacy

import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.core.store.utils.Address
import scala.collection.{JavaConverters, mutable}
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.concurrent.{Await, ExecutionContext, Future}

/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
trait ReplicaSystemFactory {

	type System <: ReplicaSystem

	def create(host : Address, others : Seq[Address], timeout : Duration) : System

	def create(config : Config) : System = {
		val host : Address =
			Address.parse(config.getString("consys.address"))
		val others : Seq[Address] =
			JavaConverters.asScalaBuffer(config.getStringList("consys.others"))
				.map(Address.parse)
  		  .filter(address => address != host)
		val timeout : Duration =
			Duration.fromNanos(config.getDuration("consys.timeout").toNanos)

		create(host, others, timeout)
	}

	def create(configPath : String) : System = {
		val config : Config = ConfigFactory.load(configPath)
		create(config)
	}

	def spawn(configPath : String)(f : System => Any)(implicit executor : ExecutionContext) : Unit = {
		Future {
			val replicaSystem = create(configPath)
			try {
				f(replicaSystem)
			} catch {
				case e => e.printStackTrace
			} finally {
				replicaSystem.close()
			}
		}
	}

	/**
	 * Creates a sequence of replica systems in one JVM. This method can be used
	 * to create replica systems that are used for testing.
	 *
	 * @param hosts A sequence of addresses for all replica systems.
	 * @return A sequence of replica systems.
	 */
	def createForTesting(hosts : Seq[Address]) : Seq[System] = {
		val replicaSystems : mutable.ArrayBuffer[System] = new mutable.ArrayBuffer(hosts.size)

		implicit val ctx : ExecutionContext = ExecutionContext.global

		val unresolved : mutable.ArrayBuffer[Future[System]] = new mutable.ArrayBuffer(hosts.size)

		for (i <- hosts.indices) {
			unresolved += Future { create(
				host = hosts(i),
				others = hosts,
				timeout = FiniteDuration(60, "s")
			)
			}
		}

		for (i <- hosts.indices) {
			replicaSystems += Await.result(unresolved(i), FiniteDuration(60, "s"))
		}

		replicaSystems
	}

	/**
	 * Creates a sequence of replica systems in one JVM. This method can be used
	 * to create replica systems that are used for testing.
	 *
	 * @param numOfReplicas The number of replicas to create
	 * @return A sequence of replica systems.
	 */
	def createForTesting(numOfReplicas : Int) : Seq[System] = {
		createForTesting((0 until numOfReplicas).map(idx => Address("127.0.0.1", 8331 + idx)))
	}

}
