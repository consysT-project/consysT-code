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


	def commit[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updateWrites : Iterable[store.WriteUpdate]
	) : CommitStatus	= {

		updateWrites.foreach(write => {
			write.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.pending, store.isolationLevels.readCommitted)
		})

		txWrite.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.committed, store.isolationLevels.readCommitted)

		return Success
	}


	//true when the row has been committed, false if the row has been aborted/deleted
	def isRowCommitted[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	  session : Session,
	  store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		currentTxid : Id,
	  row : store.DataRow
	) : CommitStatus = {

		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.isolationLevels.readCommitted, "row has wrong isolation level")

		val txStatus = row.txStatus

		//1. If the read value does not belong to a transaction or the transaction has been committed
		if (txStatus == store.txStatuses.committed) {
			return Success
		}

		assert(row.txid.isDefined, "there has to be a txid at a rc isolated row")
		val txid = row.txid.get.id

		val selectTxResult = session.execute(
			select.all().from(store.keyspace.dataTable.name)
  			.where(QueryBuilder.eq("key", store.keys.transactionKey))
  			.and(QueryBuilder.eq("id", txid))
		)

		val selectTxRow = selectTxResult.one()

		if (selectTxRow == null) {
			//There was no transaction row, hence we cannot commit the read yet
			return Abort("there was no row found for the transaction")
		}

		val txRow = store.makeDataRow(selectTxRow)

		if (txRow.txStatus == store.txStatuses.committed) {
			//Performance: set the status to committed for further reads
			session.execute(
				update(store.keyspace.dataTable.name)
  				.`with`(set("txstatus", store.txStatuses.committed))
  				.where(QueryBuilder.eq("key", row.key))
  				.and(QueryBuilder.eq("id", row.id))
			)
			return Success
		}

		//The status of the transaction is not committed.
		return Abort("the matching transaction was not committed yet")
	}
}
