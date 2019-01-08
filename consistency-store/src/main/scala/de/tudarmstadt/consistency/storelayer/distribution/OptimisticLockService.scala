package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait OptimisticLockService[Id, Key] {
	self : SessionService[Id, Key, _, _, _, _] =>

	/* class definitions */
	case class LockDescription(key : Key, txid : Option[TxRef], reads : Set[TxRef])


	/* returns None if the key was not used by another transaction, else returns the txid. */
	def lockIfEmpty(key : Key, txid : Id) : Option[LockDescription]

	/* locks a key if it was locked by another tx before */
	def lockIfOther(key : Key, txid : Id, otherTxid : Option[Id], otherReads : Set[Id]) : Option[LockDescription]

	def addReadLock(key : Key, txid : Id) : Option[Id]

	def releaseLockAndAddRead(key : Key, txid : Id, newReadTxid : Id) : Option[Id]

	def releaseLock(key : Key, txid : Id) : Option[Id]

}
