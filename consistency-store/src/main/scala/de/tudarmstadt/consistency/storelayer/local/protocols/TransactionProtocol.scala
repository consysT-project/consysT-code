package de.tudarmstadt.consistency.storelayer.local.protocols

import de.tudarmstadt.consistency.storelayer.distribution.StoreService
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol.CommitStatus

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait TransactionProtocol[Id, Key, Data, TxStatus, Isolation, Consistency] {

	val store : StoreService[Id, Key, Data, TxStatus, Isolation, Consistency]
	import store._

	def commitWrites(txWrite : TxWrite, updWrites : Iterable[DataWrite]) : CommitStatus

	/**
		*
		* @param txid an optional id of the transaction that reads the row
		* @param row the row that is checked whether it is committed
		* @return the status of the operation
		*/
	def readIsObservable(txid : Option[Id], row : OpRow) : CommitStatus

}


object TransactionProtocol {

	trait CommitStatus {
		def isSuccess : Boolean
	}
	//The transaction successfully committed
	case object Success extends CommitStatus {
		override def isSuccess : Boolean = true
	}
	//The transaction has been aborted and changes have been rolled back.
	case class Abort(message : String) extends CommitStatus {
		override def isSuccess : Boolean = false
	}
}