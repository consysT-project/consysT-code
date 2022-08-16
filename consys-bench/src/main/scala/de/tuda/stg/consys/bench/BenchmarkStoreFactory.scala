package de.tuda.stg.consys.bench

import com.typesafe.config.Config
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.core.store.utils.SinglePortAddress


trait BenchmarkStoreFactory[StoreType <: DistributedStore with BarrierStore] extends (Config => StoreType)

object BenchmarkStoreFactory {

	val akkaStoreFactory : BenchmarkStoreFactory[AkkaStore] = (config : Config) => {
		val store = AkkaStore.fromAddress(
			host = config.getString("consys.bench.akka.host"),
			akkaPort = config.getInt("consys.bench.akka.akkaPort"),
			zookeeperPort = config.getInt("consys.bench.akka.zookeeperPort"),
			timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.akka.timeout"))
		)
		val otherReplicas = config.getStringList("consys.bench.akka.otherReplicas")
		otherReplicas.forEach(s => {
			val addr = SinglePortAddress.parse(s)
			store.addOtherReplica(addr.hostname, addr.port)
		})
		store
	}

	val cassandraStoreFactory : BenchmarkStoreFactory[CassandraStore] = (config : Config) => {
		val initialize = config.getBoolean("consys.bench.cassandra.initialize")

		val store = if (initialize) {
			CassandraStore.fromAddress(
				host = config.getString("consys.bench.cassandra.host"),
				cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
				zookeeperPort = config.getInt("consys.bench.cassandra.zookeeperPort"),
				timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.cassandra.timeout")),
				initialize = true
			)
		} else {
			//TODO: Does this work without a barrier?
			CassandraStore.fromAddress(
				host = config.getString("consys.bench.cassandra.host"),
				cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
				zookeeperPort = config.getInt("consys.bench.cassandra.zookeeperPort"),
				timeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.cassandra.timeout")),
				initialize = false
			)
		}
		store
	}

}
