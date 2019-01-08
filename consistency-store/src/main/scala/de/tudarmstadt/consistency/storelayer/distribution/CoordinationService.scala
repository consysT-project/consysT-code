package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait CoordinationService[Id, TxStatus, Isolation] {
	self : SessionService[Id, _, _, TxStatus, Isolation, _] =>

	def addNewTransaction(txid : Id, txStatus : TxStatus, isolation : Isolation) : Boolean

	/**
		* Aborts a transaction if it was pending.
		*
		* @param txid the transaction to be aborted
		* @return True, if the transaction has been aborted.
		*/
	def abortIfPending(txid : Id) : Boolean

	/**
		* Commits a transaction if it was pending.
		*
		* @param txid the transaction to be committed
		* @return True, if the transaction has been committed.
		*/
	def commitIfPending(txid : Id) : Boolean

}
