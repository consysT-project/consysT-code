package de.tuda.stg.consys.bench

import com.typesafe.config.Config
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore

object BenchmarkFactories {

	trait BenchmarkFactory[StoreType <: DistributedStore with BarrierStore] {
		def apply(name : String, config : Config) : StoreType
	}

}
