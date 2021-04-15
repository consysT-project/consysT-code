package de.tuda.stg.consys.core.store.extensions.store

import de.tuda.stg.consys.core.store.extensions.store.LockingStore.DistributedLock

/**
 * Trait for stores that require a locking mechanism.
 */
trait LockingStore extends DistributedStore {
	/** The concrete type of locks handled by this store. */
	type LockType <: DistributedLock

	/**
	 * Returns a lock for the given address. This method does not change
	 * the state of the lock.
	 *
	 * @param addr The address of the object which the lock is for.
	 * @return A lock for the object.
	 */
	def lockFor(addr : Addr) : LockType
}

object LockingStore {

	/**
	 * A distributed lock that can be acquired or released.
	 */
	trait DistributedLock {
		/** Acquires the lock */
		def acquire() : Unit
		/** Releases the lock */
		def release() : Unit
	}
}