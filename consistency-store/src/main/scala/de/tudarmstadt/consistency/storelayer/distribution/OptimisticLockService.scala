package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait OptimisticLockService[Id, Txid, Key] {
	self : SessionService[Id, Txid, Key, _, _, _, _] =>

	/* class definitions */
	case class LockDescription(key : Key, txid : Option[TxRef], reads : Set[TxRef])


	/* returns None if the key was not used by another transaction, else returns the txid. */
	def lockIfEmpty(key : Key, txid : Txid) : Option[LockDescription]

	/* locks a key if it was locked by another tx before */
	def lockIfOther(key : Key, txid : Txid, otherTxid : Option[Txid], otherReads : Set[Txid]) : Option[LockDescription]

	def addReadLock(key : Key, txid : Txid) : Option[Txid]

	def releaseLockAndAddRead(key : Key, txid : Txid, newReadTxid : Txid) : Option[Txid]

	def releaseLock(key : Key, txid : Txid) : Option[Txid]

}
