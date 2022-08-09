package de.tuda.stg.consys.core.store.extensions.coordination

import de.tuda.stg.consys.core.store.extensions.DistributedStore
import scala.concurrent.duration.{Duration, FiniteDuration}

/**
 * A store that supports barriers.
 */
trait BarrierStore extends DistributedStore {
	/** Enters a barrier with the given name. */
	def barrier(name : String, count : Int, timeout : FiniteDuration) : Unit

	def barrier(name : String, count : Int) : Unit = {
		barrier(name, count, timeout)
	}
}
