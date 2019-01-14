package de.tudarmstadt.consistency.storelayer.local.protocols

import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol.{Abort, CommitStatus, Success}

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait ReadUncommittedTransactionProtocol[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] extends TransactionProtocol[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {

	override val store : SessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with DatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with TxStatusBindings[TxStatus]
		with IsolationBindings[Isolation]

	import store._


	override def commitWrites(txWrite : TxWrite, dataWrites : Iterable[DataWrite]) : CommitStatus	= {
		assert(dataWrites.isEmpty, "read uncommitted transaction cannot contain buffered writes")
		writeTx(txWrite, TxStatus.COMMITTED, Isolation.RU)

		return Success
	}


	def readIsObservable(currentTxid : Option[Txid], row : OpRow) : CommitStatus = {
		return Success
	}

}
