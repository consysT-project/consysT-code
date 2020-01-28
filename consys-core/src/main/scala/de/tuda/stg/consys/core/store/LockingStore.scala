package de.tuda.stg.consys.core.store

import LockingStore.DistributedLock

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingStore extends DistributedStore {
	type LockType <: DistributedLock

	def lockFor(addr : Addr) : LockType
}

object LockingStore {

	trait DistributedLock {
		def acquire() : Unit
		def release() : Unit
	}
}