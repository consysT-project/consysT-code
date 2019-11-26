package de.tuda.stg.consys.core.actors

import de.tuda.stg.consys.core.Utils.TxMutex

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait Lockable[T <: AnyRef] {

	private val txMutex = new TxMutex()

	/**
	 * Acquires the lock for this object. If the lock is currently taken by another transaction,
	 * then this will wait until the lock is available again.
	 *
	 * @param txid The transaction that wants to acquire the lock.
	 */
	private[actors] def lock(txid : Long) : Unit = {
		txMutex.lockTxid(txid)
	}

	private[actors] def unlock(txid : Long) : Unit = {
		txMutex.unlockTxid(txid)
	}

	private[actors] def unlockAll(txid : Long) : Unit = {
		txMutex.unlockAllTxid(txid)
	}

	/**
	 * Tries to acquire the lock for this object. If the lock has been acquired then this returns true,
	 * else it returns false.
	 *
	 * @param txid The transaction that wants to acquire the lock.
	 */
	private[actors] def tryLock(txid : Long) : Boolean = {
		txMutex.tryLockTxid(txid)
	}

	private[actors] def unsafeCompareTxid(txid : Long) : Boolean = {
		val currentTxid = txMutex.unsafeCurrentTxid
		currentTxid.isDefined && currentTxid.get == txid
	}

}
