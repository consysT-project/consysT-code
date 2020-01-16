package de.tuda.stg.consys.core.store

import de.tuda.stg.consys.core.store.LockingTransactionContext.DistributedLock

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingStore extends DistributedStore {
	type LockType <: DistributedLock
	def retrieveLockFor(addr : Addr) : LockType
}
