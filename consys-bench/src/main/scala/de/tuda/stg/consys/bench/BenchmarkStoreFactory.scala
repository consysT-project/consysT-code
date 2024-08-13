package de.tuda.stg.consys.bench

import com.typesafe.config.Config
import de.tuda.stg.consys.core.store.CoordinationMechanism
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.core.store.utils.{MultiPortAddress, SinglePortAddress}

import scala.collection.JavaConverters
import scala.jdk.CollectionConverters


trait BenchmarkStoreFactory[StoreType <: DistributedStore with BarrierStore] extends (Config => StoreType)

object BenchmarkStoreFactory {

	val akkaStoreFactory : BenchmarkStoreFactory[AkkaStore] = (config : Config) => {
		import CollectionConverters._

		val replicas =  config.getStringList("consys.bench.akka.replicas").asScala.map(s => MultiPortAddress.parse(s))
		val processId = config.getInt("consys.bench.processId")
		val address = replicas(processId)

		val store = AkkaStore.fromAddress(
			host = address.hostname,
			akkaPort = address.port1,
			coordinationMechanism = CoordinationMechanism.ETCD(address.port2),
			timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.akka.timeout"))
		)

		replicas.foreach(addr => {
			store.addOtherReplica(addr.hostname, addr.port1)
		})

		store
	}

	val akkaClusterStoreFactory : BenchmarkStoreFactory[AkkaClusterStore] =  (config : Config) => {
		import CollectionConverters._

		val replicas =  config.getStringList("consys.bench.akkacluster.replicas").asScala.map(s => MultiPortAddress.parse(s))
		val processId = config.getInt("consys.bench.processId")
		val address = replicas(processId)

		val akkaReplicas = replicas.map(mpa => SinglePortAddress(mpa.hostname, mpa.port1))

		val store = AkkaClusterStore.fromAddress(
			host = address.hostname,
			akkaPort = address.port1,
			coordinationMechanism = CoordinationMechanism.ETCD(address.port2),
			timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.akkacluster.timeout")),
			nodes = akkaReplicas
		)

		store
	}

	val cassandraStoreFactory : BenchmarkStoreFactory[CassandraStore] = (config : Config) => {
		val initialize = config.getBoolean("consys.bench.cassandra.initialize")

		val store = if (initialize) {
			CassandraStore.fromAddress(
				host = config.getString("consys.bench.cassandra.host"),
				cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
				coordinationMechanism = CoordinationMechanism.ETCD(config.getInt("consys.bench.cassandra.zookeeperPort")),
				datacenter = config.getString("consys.bench.cassandra.datacenter"),
				timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.cassandra.timeout")),
				initialize = true
			)
		} else {
			//TODO: Does this work without a barrier?
			CassandraStore.fromAddress(
				host = config.getString("consys.bench.cassandra.host"),
				cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
				coordinationMechanism = CoordinationMechanism.ETCD(config.getInt("consys.bench.cassandra.zookeeperPort")),
				datacenter = config.getString("consys.bench.cassandra.datacenter"),
				timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.cassandra.timeout")),
				initialize = false
			)
		}
		store
	}
}
