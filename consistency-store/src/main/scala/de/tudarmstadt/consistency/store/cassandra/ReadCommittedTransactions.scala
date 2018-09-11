package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.querybuilder.QueryBuilder.select
import com.datastax.driver.core.{ConsistencyLevel, Session}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.TxRef

import scala.reflect.runtime.universe._

/*
TODO: The current implementation of read committed isolation has still some problems.

* it allows dirty reads
* it allows dirty writes

 */
/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object ReadCommittedTransactions {


	def commit[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updateWrites : Iterable[store.WriteUpdate]
	): CommitStatus[Id, Key]	= {

		import CommitStatus._

		try {
			updateWrites.foreach(write => {
				write.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.committed, store.isolationLevels.readCommitted)
			})

			txWrite.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.committed, store.isolationLevels.readCommitted)


		} catch {
			//TODO: Do proper error handling here
			case e : Exception => return Error(txWrite.tx.id, e)
		}

		return Success(txWrite.tx.id, updateWrites.map(_.upd.toRef))
	}


	//true when the row has been committed, false if the row has been aborted/deleted
	def commitRow[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	  session : Session,
	  store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
	  row : store.DataRow
	) : Boolean = {

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.isolationLevels.readCommitted, "row has wrong isolation level")

		val txStatus = row.txStatus

		//1. If the read value does not belong to a transaction or the transaction has been committed
		if (txStatus == store.txStatuses.committed) {
			return true
		}

		return false
	}


	def read[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		key : Key
	): ReadStatus[Id, Key, Data] = {

		import ReadStatus._


		//Retrieve the maximum id for a given key
		val maxResult = session.execute(select().max("id")
			.from(store.keyspace.dataTable.name)
			.where(QueryBuilder.eq("key", key))
		)

		val maxRow = maxResult.one()

		if (maxRow == null) {
			//			assert(false, "did not retrieve anything from database")
			return NotFound(key, s"no entry for $key in database")
		}


		val readId = maxRow.get("system.max(id)", store.idType)

		if (readId == null) {
			//			assert(false, "no rows left for key " + key)
			return NotFound(key, s"no entry for $key in database")
		}

		//Retrieve the row with the maximum id
		val readResult = session.execute(select().all()
			.from(store.keyspace.dataTable.name)
			.where(QueryBuilder.eq("id", readId))
			.and(QueryBuilder.eq("key", key))
		)

		/*TODO: Another possibility would be to use the user defined maxRow which returns the complete row (in the aggregation) instead of just one column.

		I have to make weigh the differences between these to possibilities.

		select maxRow(id, key, data, deps, txid, consistency) from t_data where key = 'x';

		 */

		val readRow = readResult.one()

		if (readRow == null) {
			//			assert(false, "did not retrieve anything from database")
			return NotFound(key, s"no entry for $key in database anymore (it may have been removed concurrently)")
			//TODO: Retry here???
		}

		val dataRow = store.CassandraRow(readRow)



		return Success(key, dataRow.id, dataRow.data, dataRow.deps)
	}

}
