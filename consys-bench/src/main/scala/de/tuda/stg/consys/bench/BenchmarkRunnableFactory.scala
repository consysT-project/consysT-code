package de.tuda.stg.consys.bench

import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore

trait BenchmarkRunnableFactory {
	def create(store : DistributedStore with BarrierStore, config : BenchmarkConfig) : BenchmarkRunnable
}
