package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, Session, WriteType}
import de.tudarmstadt.consistency.store._

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
		txWrite : store.WriteTx,
		updWrites : Iterable[store.WriteUpdate]
	) : CommitStatus[Id, Key]	= {

		import CommitStatus._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val keyspace = store.keyspace
		val txid = txWrite.tx.id

		/* Handle writes */
		try { //Catch exceptions when running CAS queries

			//3. Add a new entry into the transaction table (lightweight transaction)
			val txInsertResult = session.execute(
				insertInto(keyspace.txTable.name)
					.values(
						Array[String]("txid", "status", "isolation"),
						Array[AnyRef](txid.asInstanceOf[AnyRef], store.txStatuses.pending.asInstanceOf[AnyRef], store.isolationLevels.snapshotIsolation.asInstanceOf[AnyRef])
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
			for (write <- updWrites) {

				val updateKeyResult = session.execute(
					update(keyspace.keyTable.name)
						.`with`(set("txid", txid))
						.where(QueryBuilder.eq("key", write.upd.key))
						.onlyIf(QueryBuilder.eq("txid", null))
  					.and(QueryBuilder.eq("reads", null))
						.setConsistencyLevel(ConsistencyLevel.ALL)
				)

				val row = updateKeyResult.one()

				if (row == null) {
					return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
				}

				//If the lock was not set
				if (!rowWasApplied(row)) {
					val otherTxid = row.get("txid", store.idType)
					val otherReads : java.util.Set[Id] = row.getSet("reads", store.idType.getJavaType)

					//4.a. Set the other running transaction to aborted if it uses the key
					if (otherTxid != null) {

						val updateOtherTxResult = session.execute(
							update(keyspace.txTable.name)
								.`with`(set("status", store.txStatuses.aborted))
								.where(QueryBuilder.eq("txid", otherTxid))
								.onlyIf(QueryBuilder.ne("status", store.txStatuses.committed))
								.setConsistencyLevel(ConsistencyLevel.ALL)
						)
						//It does not really matter what the outcome here is, IF the update was executed at all.
						//The txstatus is then either aborted or committed. In both cases we can safely change the
						//keys lock.
						//TODO: Check whether the query was executed at all?
					}


					//4.b. Set all transactions that read a key
					if (!otherReads.isEmpty) { //if reads == null in cassandra then otherReads will be empty
						//Abort all pending transactions that read any of the keys.
						for (rid <- JavaConverters.iterableAsScalaIterable(otherReads)) {
							if (rid != txid) { //it is ok for our transaction to read a value.
								val updateOtherTxResult = session.execute(
									update(keyspace.txTable.name)
										.`with`(set("status", store.txStatuses.aborted))
										.where(QueryBuilder.eq("txid", rid))
										.onlyIf(QueryBuilder.ne("status", store.txStatuses.committed))
										.setConsistencyLevel(ConsistencyLevel.ALL)
								)
								//It does not really matter what the outcome here is, IF the update was executed at all.
								//The txstatus is then either aborted or committed. In both cases we can safely change the
								//keys lock.
								//TODO: Check whether the query was executed at all?
							}
						}
					}

					//Now, we aborted all pending transactions that locked the key (either as read or write).

					//Continue to lock the key for this transactions.
					val updateKeyAgainResult = session.execute(
						update(keyspace.keyTable.name)
							.`with`(set("txid", txid))
  						.and(set("reads", null)) //TODO: Remove all reads or retain txid as read?
							.where(QueryBuilder.eq("key", write.upd.key))
							.onlyIf(QueryBuilder.eq("txid", otherTxid))
  						.and(QueryBuilder.eq("reads", otherReads))
							.setConsistencyLevel(ConsistencyLevel.ALL)
					)

					val rowAgain = updateKeyAgainResult.one()

					if (rowAgain == null) {
						return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
					}

					if (!rowWasApplied(rowAgain)) {
						//If we could not change the key (because another transaction changed it before us) then abort
						return Abort(txid, s"another tx is accessing lock for ${write.upd.key}")
					}
				}
			}

			//5. Add the data to the data table
			//5.1. Get the (already generated) ids foreach write

			//5.2 Add a data entry for each write
			updWrites.foreach(write => {
				write.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.pending, store.isolationLevels.snapshotIsolation)
			})

			//5.3. Add a transaction record to the data table
			txWrite.writeData(session, ConsistencyLevel.ONE)(store.txStatuses.pending, store.isolationLevels.snapshotIsolation)


			//6. Mark transaction as committed
			val updateTxComittedResult = session.execute(
				update(keyspace.txTable.name)
					.`with`(set("status", store.txStatuses.committed))
					.where(QueryBuilder.eq("txid", txid))
					.onlyIf(QueryBuilder.ne("status", store.txStatuses.aborted))
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)

			if (!updateTxComittedResult.wasApplied()) {
				return Abort(txid, "the transaction has been aborted by a conflicting transaction before being able to commit")
			}

			return Success[Id, Key](txid, updWrites.map(_.upd.toRef))
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
		 txid : Id,
		 row : store.DataRow
	 ) : Boolean = {

		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.isolationLevels.snapshotIsolation, "row has wrong isolation level")

		val readTxid = row.cassandraTxid
		val txStatus = row.txStatus


		//2.a If the read value does not belong to a transaction or the transaction has been committed
		if (txStatus == store.txStatuses.committed) {
			return true
		}

		val readId = row.id
		val readKey = row.key

		//2.b if the row is a transaction row, return
		//2.c If the read value does not belong to a transaction or the transaction has been committed
		if (readTxid == null || readKey == null) {
			//Performance optimization: set the tx status of the read row to committed
			session.execute(
				update(store.keyspace.dataTable.name)
					.`with`(set("txstatus", store.txStatuses.committed))
					.where(QueryBuilder.eq("key", readKey))
					.and(QueryBuilder.eq("id", readId))
			)

			return true
		}

		//3. Abort the transaction readTxid if it is not committed
		val abortReadTxResult = session.execute(
			update(store.keyspace.txTable.name)
				.`with`(set("status", store.txStatuses.aborted))
				.where(QueryBuilder.eq("txid", readTxid))
				.onlyIf(QueryBuilder.ne("status", store.txStatuses.committed))
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val abortReadTxRow = abortReadTxResult.one()

		if (abortReadTxRow == null) {
			assert(false, "transaction has not been found in db")
		}

		//3.a If the tx is aborted, then the row is aborted
		if (rowWasApplied(abortReadTxRow)) {
			//Performance: the data entry can be deleted
			session.execute(
				delete()
					.from(store.keyspace.dataTable.name)
					.where(QueryBuilder.eq("id", readId))
					.and(QueryBuilder.eq("key", readKey))
			)
			return false
		}

		//3.b The transaction (with row) has been committed. Add a read lock.
		val updateReadKeys = session.execute(
			update(store.keyspace.keyTable.name)
				.`with`(add("reads", txid))
				.where(QueryBuilder.eq("key", readKey))
				.onlyIf(QueryBuilder.eq("txid", null))
		)

		val updateReadKeysRow = updateReadKeys.one()

		if (updateReadKeysRow == null) {
			assert(false, "row was null")
		}

		//3.c if there is another transaction currently holding the write lock, abort that transaction
		if (!rowWasApplied(updateReadKeysRow)) {
			val otherTxid = updateReadKeysRow.get("txid", store.idType)

			val abortOtherTxResult = session.execute(
				update(store.keyspace.txTable.name)
					.`with`(set("status", store.txStatuses.aborted))
					.where(QueryBuilder.eq("txid", otherTxid))
					.onlyIf(QueryBuilder.ne("status", store.txStatuses.committed))
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)
			//The other transaction currently holding the lock is now either committed or aborted.
			//In both cases we can release the lock.

			val releaseOtherTxidLock = session.execute(
				update(store.keyspace.keyTable.name)
  				.`with`(set("txid", null))
  				.and(add("reads", txid))
  				.where(QueryBuilder.eq("key", readKey))
  				.onlyIf(QueryBuilder.eq("txid", otherTxid))
			)

			val releaseOtherTxidLockRow = releaseOtherTxidLock.one()

			if (releaseOtherTxidLockRow == null) {
				assert(false, "row was null")
			}

			//Some other transaction is currently messing with the variable lock.
			if (!rowWasApplied(releaseOtherTxidLockRow)) {
				//Give up
				return false
			}
		}

		return true
	}
}
