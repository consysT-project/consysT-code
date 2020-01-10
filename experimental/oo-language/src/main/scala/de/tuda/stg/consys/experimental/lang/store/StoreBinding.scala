package de.tuda.stg.consys.experimental.lang.store

import com.typesafe.config.Config
import de.tuda.stg.consys.core.Address
import de.tuda.stg.consys.experimental.lang.store.cassandra.CassandraStore

import scala.collection.JavaConverters
import scala.concurrent.duration.Duration

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
object StoreBinding {

	def create(config : Config) : CassandraStore = {
		val host : Address =
			Address.parse(config.getString("consys.address"))

		val zkPort = config.getInt("consys.zookeeper.port")
		val cassandraPort = config.getInt("consys.cassandra.port")

		val timeout : Duration =
			Duration.fromNanos(config.getDuration("consys.timeout").toNanos)

		null
	}

}
