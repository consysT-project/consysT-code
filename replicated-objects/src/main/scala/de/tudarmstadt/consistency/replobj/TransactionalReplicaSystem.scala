package de.tudarmstadt.consistency.replobj

/**
	* Provides functionality for thze current thread to check and modify his transaction status.
	*
	* @author Mirko Köhler
	*/
trait TransactionalReplicaSystem[Addr] extends ReplicaSystem[Addr] {

	type Tx

	def hasCurrentTransaction : Boolean

	def getCurrentTransaction : Tx

	def newTransaction(consistencyLevel : ConsistencyLevel) : Unit

	def commitTransaction() : Unit

	def setCurrentTransaction(tx : Tx) : Unit

	/**
		* Clears the current state of the transaction and resets it to fresh
		*/
	def clearTransaction() : Unit

}
