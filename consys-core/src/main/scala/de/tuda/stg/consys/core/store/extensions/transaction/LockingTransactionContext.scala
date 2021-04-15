package de.tuda.stg.consys.core.store.extensions.transaction

import de.tuda.stg.consys.core.store.extensions.store.LockingStore
import de.tuda.stg.consys.core.store.{Store, TransactionContext}
import scala.collection.mutable

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingTransactionContext[StoreType <: Store with LockingStore] extends TransactionContext[StoreType] {

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
