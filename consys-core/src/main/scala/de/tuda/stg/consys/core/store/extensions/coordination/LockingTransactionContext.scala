package de.tuda.stg.consys.core.store.extensions.coordination

import de.tuda.stg.consys.core.store.{Store, TransactionContext}

import scala.collection.mutable

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingTransactionContext[StoreType <: Store] extends TransactionContext[StoreType] {

	private val acquiredLocks : mutable.Map[StoreType#Addr, DistributedLock] = mutable.HashMap.empty

	protected def createLockFor(addr : StoreType#Addr) : DistributedLock

	def acquireLock(addr : StoreType#Addr) : Unit = {
		if (!acquiredLocks.contains(addr)) {
			val lock = createLockFor(addr)
			lock.acquire()
			acquiredLocks.put(addr, lock)
		}
	}

	def releaseLock(addr : StoreType#Addr) : Unit = acquiredLocks.get(addr) match {
		case None =>
		case Some(lock) =>
			lock.release()
			acquiredLocks.remove(addr)
	}

	def locks : Iterator[DistributedLock] = acquiredLocks.valuesIterator
}

