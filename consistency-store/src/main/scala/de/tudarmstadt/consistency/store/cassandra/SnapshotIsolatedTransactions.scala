package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, Session, WriteType}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.utils.Log

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object SnapshotIsolatedTransactions {



	def commit[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txRef : TxRef[Id],
		updates : Set[Update[Id, Key, Data]],
		result : Return
	) : CommitStatus[Id, Key, Return]	= {

		import CommitStatus._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val keyspace = store.keyspace
		val txid = txRef.id

		/* Handle writes */
		try { //Catch exceptions when running CAS queries

			//3. Add a new entry into the transaction table (lightweight transaction)
			val txInsertResult = session.execute(
				insertInto(keyspace.txTable.name)
					.values(
						Array[String]("txid", "status", "isolation"),
						Array[AnyRef](txid.asInstanceOf[AnyRef], store.txStatusOps.pending.asInstanceOf[AnyRef], store.isolationLevelOps.snapshotIsolation.asInstanceOf[AnyRef])
					)
					.ifNotExists()
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)

			//3.1. If the transaction id was already in use abort!
			if (!txInsertResult.wasApplied()) {
				//	assert(assertion = false, "transaction not added to the tx table")
				return Abort(txid, s"the chosen, fresh txid already exists. txid = $txid")
			}

			//4. Update all keys for writes in the key table
			updates.foreach(upd => {
				val updateKeyResult = session.execute(
					update(keyspace.keyTable.name)
						.`with`(set("txid", txid))
						.where(QueryBuilder.eq("key", upd.key))
						.onlyIf(QueryBuilder.eq("txid", null))
						.setConsistencyLevel(ConsistencyLevel.ALL)
				)

				//4.1. Set the other running transaction to aborted if it uses the key
				val row = updateKeyResult.one()

				if (row == null) {
					return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
				}

				if (!rowWasApplied(row)) {
					//gets the next row in the result set.
					var otherTxId : Id = row.get("txid", runtimeClassOf[Id])

					var retries = 10
					var failed = true

					while (retries > 0) {

						val updateOtherTxResult = session.execute(
							update(keyspace.txTable.name)
								.`with`(set("status", store.txStatusOps.aborted))
								.where(QueryBuilder.eq("txid", otherTxId))
								.onlyIf(QueryBuilder.ne("status", store.txStatusOps.committed))
								.setConsistencyLevel(ConsistencyLevel.ALL)
						)

						//4.1.1. If the transaction was already committed then it is save to just change the key
						//4.1.2. If the transaction was not committed (then it has been changed to aborted) and then it is save to just change the key
						val updateKeyAgainResult = session.execute(
							update(keyspace.keyTable.name)
								.`with`(set("txid", txid))
								.where(QueryBuilder.eq("key", upd.key))
								.onlyIf(QueryBuilder.eq("txid", otherTxId))
								.setConsistencyLevel(ConsistencyLevel.ALL)
						)

						val rowAgain = updateKeyAgainResult.one()

						if (rowAgain == null) {
							return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
						}

						if (rowWasApplied(rowAgain)) {
							retries = 0
							failed = false
						} else {
							//If we could not change the key (because another transaction changed it before us) retry it again
							retries = retries - 1
							otherTxId = rowAgain.get("txid", runtimeClassOf[Id])
						}

					}

					//If we already retried to change the key X times without success, give up
					if (failed) {
						//assert(false, "was unable to lock the key")
						return Abort(txid, s"could not get a lock on key ${upd.key}")
					}
				}
			})

			//5. Add the data to the data table
			//5.1. Get the (already generated) ids foreach write
			val updatedIds : Set[UpdateRef[Id, Key]] = updates.map(_.toRef)

			//5.2 Add a data entry for each write
			updates.foreach(upd => {

				val Update(id, key, data, _, deps) = upd

				store.writeData(
					session, ConsistencyLevel.ONE
				)(
					id, key, data, deps, Some(txRef), store.txStatusOps.pending, store.consistencyLevelOps.sequential, store.isolationLevelOps.snapshotIsolation
				)


			})

			//5.3. Add a transaction record to the data table
			store.writeNullData(
				session, ConsistencyLevel.ONE
			)(
				txid, store.keyOps.transactionKey, updatedIds, Some(txRef), store.txStatusOps.pending, store.consistencyLevelOps.sequential, store.isolationLevelOps.snapshotIsolation
			)


			//6. Mark transaction as committed
			val updateTxComittedResult = session.execute(
				update(keyspace.txTable.name)
					.`with`(set("status", store.txStatusOps.committed))
					.where(QueryBuilder.eq("txid", txid))
					.onlyIf(QueryBuilder.eq("status", store.txStatusOps.pending))
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)

			if (!updateTxComittedResult.wasApplied()) {
				return Abort(txid, "the transaction has been aborted by a conflicting transaction before being able to commit")
			}

			return Success[Id, Key, Return](txid, updates.map(_.toRef), result)
		} catch {
			case e : WriteTimeoutException => e.getWriteType match {
				case WriteType.CAS => return Abort(txid, e.getMessage)
				case _ => return Error(txid, e)
			}
		}
	}


	//true when the row has been committed, false if the row has been aborted/deleted
	def commitRow[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	   session : Session,
	   store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	 )(
		 row : DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]
	 ) : Boolean = {

		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.isolationLevelOps.snapshotIsolation, "row has wrong isolation level")

		val readTxid = row.cassandraTxid
		val txStatus = row.txStatus

		//1. If the read value does not belong to a transaction or the transaction has been committed
		if (txStatus == store.txStatusOps.committed) {
			return true
		}

		val id = row.id
		val key = row.key

		//2. If txid != null abort the transaction
		val abortTxResult = session.execute(
			update(store.keyspace.txTable.name)
			.`with`(set("status", store.txStatusOps.aborted))
			.where(QueryBuilder.eq("txid", readTxid))
			.onlyIf(QueryBuilder.eq("status", store.txStatusOps.pending))
			.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val abortTxRow = abortTxResult.one()

		if (abortTxRow == null) {
			//			assert(false, "did not retrieve anything from database")
			Log.warn(SnapshotIsolatedTransactions.getClass, "transaction has not been found in db")
			assert(false, "transaction has not been found in db")
			return false
		}

		if (rowWasApplied(abortTxRow)) {
			//the transaction has been aborted, the data entry can be deleted
			session.execute(
				delete()
					.from(store.keyspace.dataTable.name)
					.where(QueryBuilder.eq("id", id))
					.and(QueryBuilder.eq("key", key))
			)

			return false
		}

		//2.1. If the status was not pending, we have to take further actions
		//the status of the row that should be updated
		val status = abortTxRow.get("status", runtimeClassOf[TxStatus])

		//If the transaction was committed, remove the transaction tag from the row
		if (status == store.txStatusOps.committed) {
			session.execute(
				update(store.keyspace.dataTable.name)
					.`with`(set("txstatus", store.txStatusOps.committed))
					.where(QueryBuilder.eq("id", id))
					.and(QueryBuilder.eq("key", key))
			)

			return true

		} else { //condition: if (status == store.txStatusOps.aborted) {
			session.execute(
				delete()
					.from(store.keyspace.dataTable.name)
					.where(QueryBuilder.eq("id", id))
					.and(QueryBuilder.eq("key", key))
			)

			return false
		}



	}


	def read[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		key : Key
	) : ReadStatus[Id, Key, Data] = {

		import ReadStatus._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

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

		val dataRow : CassandraRow[Id, Key, Data, TxStatus, Isolation, Consistency] = CassandraRow(readRow)

		val id = dataRow.id
		val data = dataRow.data
		val deps = dataRow.deps

		val isolation = dataRow.isolation
		val readTxid = dataRow.txid


		//1. If the read value does not belong to a transaction
		if (readTxid == null) {
			return Success(key, id, data, deps)
		}

		//2. If txid != null abort the transaction
		val abortTxResult = session.execute(update(store.keyspace.txTable.name)
			.`with`(set("status", store.txStatusOps.aborted))
			.where(QueryBuilder.eq("txid", readTxid))
			.onlyIf(QueryBuilder.eq("status", store.txStatusOps.pending))
			.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val abortTxRow = abortTxResult.one()

		if (abortTxRow == null) {
			//			assert(false, "did not retrieve anything from database")
			return NotFound(key, s"txid $readTxid has not been found in the transaction table")
		}

		if (rowWasApplied(abortTxRow)) {
			return Success(key, id, data, deps)
		}

		//2.1. If the status was not pending, we have to take further actions
		val status = abortTxRow.get("status", runtimeClassOf[TxStatus])

		//If the transaction was committed, remove the transaction tag from the row
		if (status == store.txStatusOps.committed) {

			session.execute(
				update(store.keyspace.dataTable.name)
					.`with`(set("txstatus", store.txStatusOps.committed))
					.where(QueryBuilder.eq("id", id))
					.and(QueryBuilder.eq("key", key))
			)

			return Success(key, id, data, deps)
		} else if (status == store.txStatusOps.aborted) {


			session.execute(
				delete()
					.from(store.keyspace.dataTable.name)
					.where(QueryBuilder.eq("id", id))
					.and(QueryBuilder.eq("key", key))
			)

			/*
			Alternatively, one can set the transaction status to aborted. One have to change the reading accordingly.

			session.execute(
				update(keyspace.dataTable.name)
				.`with`(set("txstatus", txStatusOps.committed))
				.where(QueryBuilder.eq("id", id))
				.and(QueryBuilder.eq("key", key))
			)
			*/

			//Recursively read the next key
			//TODO: Retry only for X times
			return read(session, store)(key)
		}

		//We handled the 3 txstates pending, committed, and aborted. We should never get here.
		//		assert(false, "unhandled transaction state: " + status)
		return Error(key, new IllegalStateException("unhandled transaction state: " + status))
	}

}
