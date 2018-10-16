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
/*
TODO: transactions may not get aborted if the committing process fails
This may lead to uncommitted data stay in the database.
It is not clear to me whether this is a tolerated behaviour.
 */
object ReadUncommittedTransactions extends TransactionProcessor {


	def commitWrites[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updateWrites : Iterable[store.WriteUpdate]
	) : CommitStatus	= {
		assert(updateWrites.isEmpty, "read uncommitted transaction cannot contain buffered writes")

		txWrite.writeData(session, ConsistencyLevel.ONE)(store.TxStatuses.COMMITTED, store.IsolationLevels.RU)

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
		return Success
	}
}
