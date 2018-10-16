package de.tudarmstadt.consistency.store.cassandra

import java.util.ConcurrentModificationException

import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, Session, WriteType}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.TransactionProcessor.{Abort, CommitStatus, Success}
import de.tudarmstadt.consistency.store.shim.EventRef.TxRef

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object SnapshotIsolatedTransactions extends TransactionProcessor {


	def commitWrites[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updWrites : Iterable[store.WriteUpdate]
	) : CommitStatus	= {

		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val keyspace = store.keyspace
		val txid = txWrite.tx.id

		/* Handle writes */
		//1. Add a new entry into the transaction table (lightweight transaction)
		val txInsertResult = session.execute(
			insertInto(keyspace.casTxTable.name)
				.values(
					Array[String]("txid", "status", "isolation"),
					Array[AnyRef](txid.asInstanceOf[AnyRef], store.TxStatuses.PENDING.asInstanceOf[AnyRef], store.IsolationLevels.SI.asInstanceOf[AnyRef])
				)
				.ifNotExists()
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val txInsertResultRow = txInsertResult.one()
		assert(txInsertResultRow != null)

		//1.a. If the transaction id was already in use abort!
		if (!rowWasApplied(txInsertResultRow)) {
			//It is possible that the transaction already has been aborted.
			//This is possible when it held a read lock and another transaction
			//wanted to access the locked key.

			//The status has to be "aborted" in this case.
			assert(txInsertResultRow.get("status", store.txStatusType) == store.TxStatuses.ABORTED)

			//In this case abort the transaction.
			return Abort(s"the transaction has already been aborted. txid = $txid")
		}

		//2. Acquire the write lock for all keys that are written by this transaction
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
			assert(row != null, s"table ${keyspace.keyTable.name} did not return a result for update query")

			//If the lock was not set
			if (!rowWasApplied(row)) {
				val otherTxid = row.get("txid", store.idType)
				val otherReads : java.util.Set[Id] = row.getSet("reads", store.idType.getJavaType)

				//2.a. Abort the transaction that held the write lock
				if (otherTxid != null) {

					val updateOtherTxResult = session.execute(
						update(keyspace.casTxTable.name)
							.`with`(set("status", store.TxStatuses.ABORTED))
							.where(QueryBuilder.eq("txid", otherTxid))
							.onlyIf(QueryBuilder.ne("status", store.TxStatuses.COMMITTED))
							.setConsistencyLevel(ConsistencyLevel.ALL)
					)
					//It does not really matter what the outcome here is, IF the update was executed at all.
					//The txstatus is then either aborted or committed. In both cases we can safely change the
					//keys lock.
					//TODO: Check whether the query was executed at all?
				}


				//2.b. Set all transactions that read a key
				if (!otherReads.isEmpty) { //if reads == null in cassandra then otherReads will be empty
					//Abort all pending transactions that read any of the keys.
					for (rid <- JavaConverters.iterableAsScalaIterable(otherReads)) {
						if (rid != txid) { //it is ok for our transaction to read a value.
							val updateOtherTxResult = session.execute(
								update(keyspace.casTxTable.name)
									.`with`(set("status", store.TxStatuses.ABORTED))
									.where(QueryBuilder.eq("txid", rid))
									.onlyIf(QueryBuilder.ne("status", store.TxStatuses.COMMITTED))
									.setConsistencyLevel(ConsistencyLevel.ALL)
							)
							//It does not really matter what the outcome here is, IF the update was executed at all.
							//The txstatus is then either aborted or committed. In both cases we can safely change the
							//keys lock.
							//TODO: Check whether the query was executed at all?
						}
					}
				}

				//2.c. Now, we aborted all pending transactions that locked the key (either as read or write).

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
				assert(rowAgain != null, s"table ${keyspace.keyTable.name} did not return a result for update query")


				if (!rowWasApplied(rowAgain)) {
					//If we could not change the key (because another transaction changed it before us) then abort
					return Abort(s"another tx is accessing lock for ${write.upd.key}")
				}
			}
		}

		//3. Add the data to the data table
		//3.a. Add a data entry for each write
		updWrites.foreach(write => {
			write.writeData(session, ConsistencyLevel.ONE)(store.TxStatuses.PENDING, store.IsolationLevels.SI)
		})

		//3.b. Add a transaction record to the data table
		txWrite.writeData(session, ConsistencyLevel.ONE)(store.TxStatuses.PENDING, store.IsolationLevels.SI)




		//4. Mark transaction as committed
		/*
		There needs to be a proper error handling procedure for the next query:
		This query does commit the transaction. An error of the query does not mean that
		no data has been written!
		We need to check whether the data has been written in case of an error in order to make
		sure whether the transaction has been committed.
		When returning an abort to the shim layer, we have to make sure that the transaction
		really has been aborted. TODO: Is the last point really that important?
		 */
		while (true) {
			try {
				val updateTxComittedResult = session.execute(
					update(keyspace.casTxTable.name)
						.`with`(set("status", store.TxStatuses.COMMITTED))
						.where(QueryBuilder.eq("txid", txid))
						.onlyIf(QueryBuilder.ne("status", store.TxStatuses.ABORTED))
						.setConsistencyLevel(ConsistencyLevel.ALL)
				)

				if (!updateTxComittedResult.wasApplied()) {
					return Abort("the transaction has been aborted by a conflicting transaction before being able to commit")
				}

				return Success
			} catch {
				//when a timeout exception with write type CAS is thrown, then it is unclear whether the write has succeeded
				//Therefore, we should retry committing the update...
				//TODO: Add some measure to avoid infinite loops
				case e : WriteTimeoutException if e.getWriteType == WriteType.CAS =>
					//Wait a bit, then retry
					Thread.sleep(300)
			}
		}

		//This code should never be executed.
		return Abort("the transaction has been aborted for unknown reasons")
	}


	def cassandraTxid[Id](txid : Option[TxRef[Id]]) : Any =
		txid.map(ref => ref.id).getOrElse(null)

	//true when the row has been committed, false if the row has been aborted/deleted
	override def readIsObservable[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
    session : CassandraSession,
    store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
  )(
    currentTxid : Option[Id],
    row : store.ReadUpdate
  ) : CommitStatus = {

		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Check whether the given row has the correct isolation level
		val isolation = row.isolation
		assert(isolation == store.IsolationLevels.SI, "row has wrong isolation level")

		val readId = row.id
		val readKey = row.key
		val readTxid = cassandraTxid(row.txid)
		val readTxStatus = row.txStatus

		//2.a If the read value does not belong to a transaction or the transaction has been committed
		if (readTxStatus == store.TxStatuses.COMMITTED) {
			return Success
		}

		//2.b if the row is a transaction row, return TODO: Why?
		//2.c If the read value does not belong to a transaction or the transaction has been committed
		if (readTxid == null) {
			//Performance optimization: set the tx status of the read row to committed
			session.execute(
				update(store.keyspace.updateDataTable.name)
					.`with`(set("txstatus", store.TxStatuses.COMMITTED))
					.where(QueryBuilder.eq("key", readKey))
					.and(QueryBuilder.eq("id", readId))
			)

			return Success
		}

		//3. Abort the transaction readTxid if it is not committed
		val abortReadTxResult = session.execute(
			update(store.keyspace.casTxTable.name)
				.`with`(set("status", store.TxStatuses.ABORTED))
				.where(QueryBuilder.eq("txid", readTxid))
				.onlyIf(QueryBuilder.ne("status", store.TxStatuses.COMMITTED))
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val abortReadTxRow = abortReadTxResult.one()
		assert(abortReadTxRow != null, "transaction has not been found in db")

		//3.a If the tx is aborted, then the row is aborted
		if (rowWasApplied(abortReadTxRow)) {
			//Performance: the data entry can be deleted
			session.execute(
				delete()
					.from(store.keyspace.updateDataTable.name)
					.where(QueryBuilder.eq("id", readId))
					.and(QueryBuilder.eq("key", readKey))
			)
			return Abort("the transaction has already been aborted")
		}

		//3.a.I If the read was not made from within another transaction, then we do not need to add a read lock.
 		if (currentTxid.isEmpty) {
			return Success
		}

		//3.b The transaction (with row) has been committed.
		val updateReadKeys = session.execute(
			update(store.keyspace.keyTable.name)
				.`with`(add("reads", currentTxid.get))
				.where(QueryBuilder.eq("key", readKey))
				.onlyIf(QueryBuilder.eq("txid", null))
		)

		val updateReadKeysRow = updateReadKeys.one()
		assert(updateReadKeysRow != null, "row was null")

		//3.c if there is another transaction currently holding the write lock, abort that transaction
		if (!rowWasApplied(updateReadKeysRow)) {
			val otherTxid = updateReadKeysRow.get("txid", store.idType)

			val abortOtherTxResult = session.execute(
				update(store.keyspace.casTxTable.name)
					.`with`(set("status", store.TxStatuses.ABORTED))
					.where(QueryBuilder.eq("txid", otherTxid))
					.onlyIf(QueryBuilder.ne("status", store.TxStatuses.COMMITTED))
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)
			//The other transaction currently holding the lock is now either committed or aborted.
			//In both cases we can release the lock.

			val releaseOtherTxidLock = session.execute(
				update(store.keyspace.keyTable.name)
					.`with`(set("txid", null))
					.and(add("reads", currentTxid.get))
					.where(QueryBuilder.eq("key", readKey))
					.onlyIf(QueryBuilder.eq("txid", otherTxid))
			)

			val releaseOtherTxidLockRow = releaseOtherTxidLock.one()
			assert(releaseOtherTxidLockRow != null, "row was null")

			//Some other transaction is currently messing with the variable lock.
			if (!rowWasApplied(releaseOtherTxidLockRow)) {
				//Give up
				return Abort("was not able to add a read lock")
			}
		}

		return Success
	}
}
