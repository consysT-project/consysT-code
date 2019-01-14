package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait CoordinationService[Txid, TxStatus, Isolation] {
	self : SessionService[_, Txid, _, _, TxStatus, Isolation, _] =>

	def addNewTransaction(txid : Txid, txStatus : TxStatus, isolation : Isolation) : Boolean

	/**
		* Aborts a transaction if it was pending.
		*
		* @param txid the transaction to be aborted
		* @return True, if the transaction has been aborted.
		*/
	def abortIfPending(txid : Txid) : Boolean

	/**
		* Commits a transaction if it was pending.
		*
		* @param txid the transaction to be committed
		* @return True, if the transaction has been committed.
		*/
	def commitIfPending(txid : Txid) : Boolean

}
