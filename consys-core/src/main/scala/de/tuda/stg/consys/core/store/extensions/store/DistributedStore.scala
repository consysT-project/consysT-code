package de.tuda.stg.consys.core.store.extensions.store

import de.tuda.stg.consys.core.store.Store
import scala.concurrent.duration.FiniteDuration

/**
 * Trait for distributed stores.
 */
trait DistributedStore extends Store {
	def timeout : FiniteDuration
}
