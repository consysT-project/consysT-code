package de.tudarmstadt.consistency.storelayer.local.protocols

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, Session}
import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol.{Abort, CommitStatus, Success}

import scala.reflect.runtime.universe._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait ReadCommittedTransactions[Id, Key, Data, TxStatus, Isolation, Consistency] extends TransactionProtocol[Id, Key, Data, TxStatus, Isolation, Consistency] {

	override val store : SessionService[Id, Key, Data, TxStatus, Isolation, Consistency]
		with DatastoreService[Id, Key, Data, TxStatus, Isolation, Consistency]
		with TxStatusBindings[TxStatus]
		with IsolationBindings[Isolation]

	import store._


	override def commitWrites(txWrite : TxWrite, dataWrites : Iterable[DataWrite]) : CommitStatus	= {
		dataWrites.foreach(write => writeData(write, TxStatus.PENDING, Isolation.RC))
		writeTx(txWrite, TxStatus.COMMITTED, Isolation.RC)

		return Success
	}



	def readIsObservable(currentTxid : Option[Id], row : OpRow) : CommitStatus = {

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == Isolation.RC, "row has wrong isolation level")

		val txStatus = row.txStatus

		//1. If the read value does belong to a transaction that has been committed
		if (txStatus == TxStatus.COMMITTED) {
			return Success
		}

		assert(row.txid.isDefined, "there has to be a txid at a rc isolated row")
		val txid = row.txid.get.id


//		val selectTxResult = session.execute(
//			select.all().from(keyspace.txDataTable.name)
//				.where(QueryBuilder.eq("id", txid))
//		)

		readTx(txid) match {
			case None =>
				return Abort(s"there was no row for transaction $txid")

			case Some(txRow) =>
				if (txRow.txStatus == TxStatus.COMMITTED) {
//					session.execute(
//						update(keyspace.updateDataTable.name)
//							.`with`(set("txstatus", TxStatuses.COMMITTED))
//							.where(QueryBuilder.eq("key", row.key))
//							.and(QueryBuilder.eq("id", row.id))
//					)

					//Performance: set the status to committed for further reads
					updateTxStatusInData(row.id, row.key, TxStatus.COMMITTED)
					return Success
				}
		}

		//The status of the transaction is not committed.
		return Abort("the matching transaction was not committed yet")
	}
}
