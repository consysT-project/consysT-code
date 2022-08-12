package de.tuda.stg.consys.bench

import com.typesafe.config.Config
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.utils.SinglePortAddress
import de.tuda.stg.consys.japi.binding.cassandra.{CassandraReplica, CassandraStoreBinding}

import scala.concurrent.duration.Duration

object StoreAdapterFactories {

	object AkkaStoreFactory extends (Config => AkkaStore) {
		override def apply(config : Config) : AkkaStore = {

			val store = AkkaStore.fromAddress(
				host = config.getString("consys.bench.akka.host"),
				akkaPort = config.getInt("consys.bench.akka.akkaPort"),
				zookeeperPort = config.getInt("consys.bench.akka.zookeeperPort"),
				timeout = config.getDuration("consys.bench.akka.timeout")
			)

			val otherReplicas = config.getStringList("consys.bench.akka.otherReplicas")
			otherReplicas.forEach(s => {
				val addr = SinglePortAddress.parse(s)
				store.addOtherReplica(addr.hostname, addr.port)
			})

			store
		}
	}

	object CassandraStoreFactory extends (Config => CassandraStore) {
		override def apply(config : Config) : CassandraStore = {

			val initialize = config.getBoolean("consys.bench.cassandra.initialize")

			val store = if (initialize) {
				CassandraStore.fromAddress(
					host = config.getString("consys.bench.cassandra.host"),
					cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
					zookeeperPort = config.getInt("consys.bench.cassandra.zookeeperPort"),
					timeout = config.getDuration("consys.bench.cassandra.timeout"),
					initialize = true
				)
			} else {
				//TODO: Does this work without a barrier?
				CassandraStore.fromAddress(
					host = config.getString("consys.bench.cassandra.host"),
					cassandraPort = config.getInt("consys.bench.cassandra.cassandraPort"),
					zookeeperPort = config.getInt("consys.bench.cassandra.zookeeperPort"),
					timeout = config.getDuration("consys.bench.cassandra.timeout"),
					initialize = false
				)
			}

			store
		}
	}

}
