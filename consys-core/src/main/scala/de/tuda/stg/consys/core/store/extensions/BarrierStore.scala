package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.extensions.store.DistributedStore
import scala.concurrent.duration.Duration

/**
 * A store that supports barriers.
 */
trait BarrierStore extends DistributedStore {
	/** Enters a barrier with the given name. */
	def barrier(name : String, timeout : Duration = timeout) : Unit
}
