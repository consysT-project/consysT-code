package de.tuda.stg.consys.core.store

import scala.collection.mutable

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingTransactionContext extends TransactionContext {

	type StoreType <: Store with LockingStore

	private val acquiredLocks : mutable.Map[StoreType#Addr, StoreType#LockType] = mutable.HashMap.empty

	def acquireLock(addr : StoreType#Addr) : Unit = {
		if (!acquiredLocks.contains(addr)) {
			val lock : StoreType#LockType = store.lockFor(addr.asInstanceOf[store.Addr] /* TODO: Why do we need this type cast? */)
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

	def locks : Iterator[StoreType#LockType] = acquiredLocks.valuesIterator
}

object LockingTransactionContext {

}
