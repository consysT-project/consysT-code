package de.tudarmstadt.consistency.storelayer.local.protocols

import de.tudarmstadt.consistency.storelayer.distribution.{IsolationBindings, SessionService, StoreService, TxStatusBindings}
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol.{Abort, CommitStatus, Success}

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait ReadUncommittedTransactions[Id, Key, Data, TxStatus, Isolation, Consistency] extends TransactionProtocol[Id, Key, Data, TxStatus, Isolation, Consistency] {

	override val store : SessionService[Id, Key, Data, TxStatus, Isolation, Consistency]
		with StoreService[Id, Key, Data, TxStatus, Isolation, Consistency]
		with TxStatusBindings[TxStatus]
		with IsolationBindings[Isolation]

	import store._


	override def commitWrites(txWrite : TxWrite, dataWrites : Iterable[DataWrite]) : CommitStatus	= {
		assert(dataWrites.isEmpty, "read uncommitted transaction cannot contain buffered writes")
		writeTx(txWrite, TxStatus.COMMITTED, Isolation.RU)

		return Success
	}


	def readIsObservable(currentTxid : Option[Id], row : OpRow) : CommitStatus = {
		return Success
	}

}
