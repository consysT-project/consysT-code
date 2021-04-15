package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.ConsysUtils.TxMutex

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait Lockable[T] {

	private val txMutex = new TxMutex()

	/**
	 * Acquires the lock for this object. If the lock is currently taken by another transaction,
	 * then this will wait until the lock is available again.
	 *
	 * @param txid The transaction that wants to acquire the lock.
	 */
	private[akka] def lock(txid : Long) : Unit = {
		txMutex.lockTxid(txid)
	}

	private[akka] def unlock(txid : Long) : Unit = {
		txMutex.unlockTxid(txid)
	}

	private[akka] def unlockAll(txid : Long) : Unit = {
		txMutex.unlockAllTxid(txid)
	}

	/**
	 * Tries to acquire the lock for this object. If the lock has been acquired then this returns true,
	 * else it returns false.
	 *
	 * @param txid The transaction that wants to acquire the lock.
	 */
	private[akka] def tryLock(txid : Long) : Boolean = {
		txMutex.tryLockTxid(txid)
	}

	private[akka] def unsafeCompareTxid(txid : Long) : Boolean = {
		val currentTxid = txMutex.unsafeCurrentTxid
		currentTxid.isDefined && currentTxid.get == txid
	}

}
