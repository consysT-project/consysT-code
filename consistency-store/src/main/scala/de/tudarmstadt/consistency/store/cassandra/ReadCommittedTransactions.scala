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
		txRef : TxRef[Id],
		updates : Set[Update[Id, Key, Data]],
		result : Return
	): CommitStatus[Id, Key, Return]	= {

		import CommitStatus._


		//TODO: Instead of computing the updated ids here, use the transaction ids from the shim layer
		try {

			updates.foreach(upd => {
				val Update(id, key, data, _, deps) = upd

				store.writeData(session, ConsistencyLevel.ONE)(
					id, key, data, deps, Some(txRef), store.txStatusOps.committed, store.consistencyLevelOps.sequential, store.isolationLevelOps.readCommitted
				)
			})

			store.writeNullData(session, ConsistencyLevel.ONE)(
				txRef.id, store.keyOps.transactionKey, updates.map(_.toRef), Some(txRef), store.txStatusOps.pending, store.consistencyLevelOps.sequential, store.isolationLevelOps.readCommitted
			)


		} catch {
			//TODO: Do proper error handling here
			case e : Exception => return Error(txRef.id, e)
		}

		return Success(txRef.id, updates.map(_.toRef), result)
	}


	//true when the row has been committed, false if the row has been aborted/deleted
	def commitRow[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	  session : Session,
	  store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
	  row : DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]
	) : Boolean = {

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.isolationLevelOps.readCommitted, "row has wrong isolation level")

		val txStatus = row.txStatus

		//1. If the read value does not belong to a transaction or the transaction has been committed
		if (txStatus == store.txStatusOps.committed) {
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


		val readId = maxRow.get("system.max(id)", runtimeClassOf[Id])

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

		val dataRow = CassandraRow[Id, Key, Data, TxStatus, Isolation, Consistency](readRow)



		return Success(key, dataRow.id, dataRow.data, dataRow.deps)
	}

}
