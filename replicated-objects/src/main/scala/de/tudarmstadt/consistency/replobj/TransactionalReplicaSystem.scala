package de.tudarmstadt.consistency.replobj

/**
	* Provides functionality for thze current thread to check and modify his transaction status.
	*
	* @author Mirko Köhler
	*/
trait TransactionalReplicaSystem[Addr, Tx] extends ReplicaSystem[Addr] {

	def hasCurrentTransaction : Boolean

	def getCurrentTransaction : Tx

//	def isNested : Boolean
//
//	def isToplevel : Boolean = !isNested

	def newTransaction(consistencyLevel : ConsistencyLevel) : Unit

	def commitTransaction() : Unit

	def setCurrentTransaction(tx : Tx) : Unit

	/**
		* Clears the current state of the transaction and resets it to fresh
		*/
	def clearTransaction() : Unit

}
