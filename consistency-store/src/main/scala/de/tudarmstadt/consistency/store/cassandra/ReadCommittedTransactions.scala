package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, Session}
import de.tudarmstadt.consistency.store.cassandra.TransactionProcessor.{Abort, CommitStatus, Success}

import scala.reflect.runtime.universe._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object ReadCommittedTransactions extends TransactionProcessor {


	def commitWrites[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updateWrites : Iterable[store.WriteUpdate]
	) : CommitStatus	= {

		updateWrites.foreach(write => {
			write.writeData(session, ConsistencyLevel.ONE)(store.TxStatuses.PENDING, store.IsolationLevels.RC)
		})

		txWrite.writeData(session, ConsistencyLevel.ONE)(store.TxStatuses.COMMITTED, store.IsolationLevels.RC)

		return Success
	}


	//true when the row has been committed, false if the row has been aborted/deleted
	def readIsObservable[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	  session : Session,
	  store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		currentTxid : Option[Id],
	  row : store.ReadUpdate
	) : CommitStatus = {
		import store._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.IsolationLevels.RC, "row has wrong isolation level")

		val txStatus = row.txStatus

		//1. If the read value does belong to a transaction that has been committed
		if (txStatus == TxStatuses.COMMITTED) {
			return Success
		}

		assert(row.txid.isDefined, "there has to be a txid at a rc isolated row")
		val txid = row.txid.get.id

		val selectTxResult = session.execute(
			select.all().from(keyspace.txDataTable.name)
  			.where(QueryBuilder.eq("id", txid))
		)

		val selectTxRow = selectTxResult.one()

		if (selectTxRow == null) {
			//There was no transaction row, hence we cannot commit the read yet
			return Abort("there was no row found for the transaction")
		}

		val txRow = store.makeTxRow(selectTxRow)

		if (txRow.txStatus == TxStatuses.COMMITTED) {
			//Performance: set the status to committed for further reads
			session.execute(
				update(keyspace.updateDataTable.name)
  				.`with`(set("txstatus", TxStatuses.COMMITTED))
  				.where(QueryBuilder.eq("key", row.key))
  				.and(QueryBuilder.eq("id", row.id))
			)
			return Success
		}

		//The status of the transaction is not committed.
		return Abort("the matching transaction was not committed yet")


	}
}
