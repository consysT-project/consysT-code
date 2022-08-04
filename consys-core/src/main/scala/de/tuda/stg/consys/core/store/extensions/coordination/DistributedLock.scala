package de.tuda.stg.consys.core.store.extensions.coordination

/**
 * A distributed lock that can be acquired or released.
 */
trait DistributedLock {
	/** Acquires the lock */
	def acquire() : Unit
	/** Releases the lock */
	def release() : Unit
}