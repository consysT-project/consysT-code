package de.tuda.stg.consys.core.store.extensions.store

import scala.concurrent.duration.Duration

/**
 * A store that supports barriers.
 */
trait BarrierStore extends DistributedStore {
	/** Enters a barrier with the given name. */
	def barrier(name : String, timeout : Duration = timeout) : Unit
}
