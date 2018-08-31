//package de.tudarmstadt.consistency.store.scala.extra.internalstore
//
//import com.datastax.driver.core.exceptions.WriteTimeoutException
//import com.datastax.driver.core.querybuilder.QueryBuilder
//import com.datastax.driver.core.utils.UUIDs
//import com.datastax.driver.core.{ConsistencyLevel, Row, Session, WriteType}
//import de.tudarmstadt.consistency.store.scala.SessionContext
//import de.tudarmstadt.consistency.store.scala.extra.internalstore.exceptions.UnsupportedIsolationLevelException
//
//import scala.collection.JavaConverters
//import scala.reflect.runtime.universe._
//
///**
//	* Created on 28.08.18.
//	*
//	* @author Mirko Köhler
//	*/
//trait SysnameSnapshotIsolatedTransactionStore[Id, Key, Data, TxStatus, Consistency, Isolation] extends SysnameCassandraStore[Id, Key, Data, TxStatus, Consistency, Isolation] {
//
//
//	override def commit[Return](session : CassandraSession, transaction : Transaction[Return], isolation : Isolation)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return] = isolation match {
//		case l if l == isolationLevelOps.snapshotIsolation =>
//			val context = new SnapshotIsolatedTransactionContext(session)
//
//			transaction(context) match {
//				case Some(result) =>
//					val commitStatus = commitWithSnapshotIsolation(session, context, result)
//					commitStatus
//				case None =>
//					//In this case we do not add anything to the database. Note that there is also no entry in the tx table for that txid.
//					return CommitStatus.Abort(context.txid, "user abort")
//			}
//
//		case _ => super.commit(session, transaction, isolation)
//	}
//
//
//	override def internalRead(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : ReadStatus[Id, Key, Data] = isolation match {
//		case  l if l == isolationLevelOps.snapshotIsolation => readWithSnapshotIsolation(session, id, key, isolation, row)
//
//		case _ => super.internalRead(session, id, key, isolation, row)
//	}
//
//
//
//	private class SnapshotIsolatedTransactionContext(val session : CassandraSession) extends TransactionContext {
//
//		//2. Retrieve a fresh transaction id
//		val txid : Id = idOps.freshId()
//
//		case class Update(id : Id, key : Key, data : Data, dependencies : Set[Id])
//
//		var nextDependencies : Set[Id] = Set.empty
//		var updates : Set[Update] = Set.empty
//
//
//		override def read(key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Option[Data] = SysnameSnapshotIsolatedTransactionStore.this.read(session, key) match {
//			case ReadStatus.Success(_, id, data) =>
//				nextDependencies = nextDependencies + id
//				Some(data)
//			case _ => None
//		}
//
//
//		override def write(key : Key, data : Data)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = {
//
//			val id = idOps.freshId() //TODO: Is it a problem that ids are generated here already?
//			updates = updates + Update(id, key, data, nextDependencies)
//			nextDependencies = Set(id)
//		}
//	}
//
//
//	private def commitWithSnapshotIsolation[Return](session : CassandraSession, transactionContext : SnapshotIsolatedTransactionContext, result : Return)
//	                                               (implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return]	= {
//		import com.datastax.driver.core.querybuilder.QueryBuilder._
//		import CommitStatus._
//
//		val txid = transactionContext.txid
//		val updates = transactionContext.updates
//
//
//		/* Handle writes */
//		try { //Catch exceptions when running CAS queries
//
//			//3. Add a new entry into the transaction table (lightweight transaction)
//			val txInsertResult = session.execute(
//				insertInto(keyspace.txTable.name)
//					.values(
//						Array[String]("txid", "status", "isolation"),
//						Array[AnyRef](txid.asInstanceOf[AnyRef], txStatusOps.pending.asInstanceOf[AnyRef], isolationLevelOps.snapshotIsolation.asInstanceOf[AnyRef])
//					)
//					.ifNotExists()
//					.setConsistencyLevel(ConsistencyLevel.ALL)
//			)
//
//			//3.1. If the transaction id was already in use abort!
//			if (!txInsertResult.wasApplied()) {
//				//	assert(assertion = false, "transaction not added to the tx table")
//				return Abort(txid, s"the chosen, fresh txid already exists. txid = $txid")
//			}
//
//			//4. Update all keys for writes in the key table
//			updates.foreach(upd => {
//				val updateKeyResult = session.execute(
//					update(keyspace.keyTable.name)
//						.`with`(set("txid", txid))
//						.where(QueryBuilder.eq("key", upd.key))
//						.onlyIf(QueryBuilder.eq("txid", null))
//						.setConsistencyLevel(ConsistencyLevel.ALL)
//				)
//
//				//4.1. Set the other running transaction to aborted if it uses the key
//				val row = updateKeyResult.one()
//
//				if (row == null) {
//					return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
//				}
//
//				if (!rowWasApplied(row)) {
//					//gets the next row in the result set.
//					var otherTxId : Id = row.get("txid", runtimeClassOf[Id])
//
//					var retries = 10
//					var failed = true
//
//					while (retries > 0) {
//
//						val updateOtherTxResult = session.execute(
//							update(keyspace.txTable.name)
//								.`with`(set("status", txStatusOps.aborted))
//								.where(QueryBuilder.eq("txid", otherTxId))
//								.onlyIf(QueryBuilder.ne("status", txStatusOps.committed))
//								.setConsistencyLevel(ConsistencyLevel.ALL)
//						)
//
//						//4.1.1. If the transaction was already committed then it is save to just change the key
//						//4.1.2. If the transaction was not committed (then it has been changed to aborted) and then it is save to just change the key
//						val updateKeyAgainResult = session.execute(
//							update(keyspace.keyTable.name)
//								.`with`(set("txid", txid))
//								.where(QueryBuilder.eq("key", upd.key))
//								.onlyIf(QueryBuilder.eq("txid", otherTxId))
//								.setConsistencyLevel(ConsistencyLevel.ALL)
//						)
//
//						val rowAgain = updateKeyAgainResult.one()
//
//						if (rowAgain == null) {
//							return Abort(txid, s"table ${keyspace.keyTable.name} did not return a result for update query")
//						}
//
//						if (rowWasApplied(rowAgain)) {
//							retries = 0
//							failed = false
//						} else {
//							//If we could not change the key (because another transaction changed it before us) retry it again
//							retries = retries - 1
//							otherTxId = rowAgain.get("txid", runtimeClassOf[Id])
//						}
//
//					}
//
//					//If we already retried to change the key X times without success, give up
//					if (failed) {
//						//assert(false, "was unable to lock the key")
//						return Abort(txid, s"could not get a lock on key ${upd.key}")
//					}
//				}
//			})
//
//			//5. Add the data to the data table
//			//5.1. Get the (already generated) ids foreach write
//			val updatedIds : Set[Id] = updates.map(upd => upd.id)
//			val depsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(updatedIds)
//
//			//5.2 Add a data entry for each write
//			updates.foreach(upd => {
//
//				val transactionContext.Update(id, key, data, deps) = upd
//
//				//Convert dependencies to Java
//				val writeDepsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(deps.union(Set(txid)))
//
//				session.execute(
//					update(keyspace.dataTable.name)
//						.`with`(set("data", data))
//						.and(set("deps", writeDepsJava))
//						.and(set("txid", txid))
//						.and(set("txstatus", txStatusOps.pending))
//						.and(set("consistency", consistencyLevelOps.sequential))
//						.and(set("isolation", isolationLevelOps.snapshotIsolation))
//						.where(QueryBuilder.eq("key", key))
//						.and(QueryBuilder.eq("id", id))
//						.setConsistencyLevel(ConsistencyLevel.ONE)
//				)
//			})
//
//			//5.3. Add a transaction record to the data table
//			session.execute(
//				update(keyspace.dataTable.name)
//					.`with`(set("data", null))
//					.and(set("deps", depsJava))
//					.and(set("txid", txid))
//					.and(set("txstatus", txStatusOps.pending))
//					.and(set("consistency", consistencyLevelOps.sequential))
//					.and(set("isolation", isolationLevelOps.snapshotIsolation))
//					.where(QueryBuilder.eq("key", "$trans"))
//					.and(QueryBuilder.eq("id", txid))
//					.setConsistencyLevel(ConsistencyLevel.ONE)
//			)
//
//			//6. Mark transaction as committed
//			val updateTxComittedResult = session.execute(
//				update(keyspace.txTable.name)
//					.`with`(set("status", txStatusOps.committed))
//					.where(QueryBuilder.eq("txid", txid))
//					.onlyIf(QueryBuilder.eq("status", txStatusOps.pending))
//					.setConsistencyLevel(ConsistencyLevel.ALL)
//			)
//
//			if (!updateTxComittedResult.wasApplied()) {
//				return Abort(txid, "the transaction has been aborted by a conflicting transaction before being able to commit")
//			}
//
//			return Success(txid, updatedIds, result)
//		} catch {
//			case e : WriteTimeoutException => e.getWriteType match {
//				case WriteType.CAS => return Abort(txid, e.getMessage)
//				case _ => return Error(txid, e)
//			}
//		}
//	}
//
//
//
//	private def readWithSnapshotIsolation(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]): ReadStatus[Id, Key, Data] = {
//
//		import ReadStatus._
//		import com.datastax.driver.core.querybuilder.QueryBuilder._
//
//		//Retrieve the maximum id for a given key
//
//
//		val readTxid = row.get("txid", runtimeClassOf[Id])
//
//		//1. If the read value does not belong to a transaction
//		if (readTxid == null) {
//			return Success(key, id, row.get("data", runtimeClassOf[Data]))
//		}
//
//		//2. If txid != null abort the transaction
//		val abortTxResult = session.execute(update(keyspace.txTable.name)
//			.`with`(set("status", txStatusOps.aborted))
//			.where(QueryBuilder.eq("txid", readTxid))
//			.onlyIf(QueryBuilder.eq("status", txStatusOps.pending))
//			.setConsistencyLevel(ConsistencyLevel.ALL)
//		)
//
//		val abortTxRow = abortTxResult.one()
//
//		if (abortTxRow == null) {
//			//			assert(false, "did not retrieve anything from database")
//			return Abort(key, s"txid $readTxid has not been found in the transaction table")
//		}
//
//		if (rowWasApplied(abortTxRow)) {
//			return Success(key, id, row.get("data", runtimeClassOf[Data]))
//		}
//
//		//2.1. If the status was not pending, we have to take further actions
//		val status = abortTxRow.get("status", runtimeClassOf[TxStatus])
//
//		//If the transaction was committed, remove the transaction tag from the row
//		if (status == txStatusOps.committed) {
//
//			session.execute(
//				update(keyspace.dataTable.name)
//					.`with`(set("txstatus", txStatusOps.committed))
//					.where(QueryBuilder.eq("id", id))
//					.and(QueryBuilder.eq("key", key))
//			)
//
//
//			return Success(key, id, row.get("data", runtimeClassOf[Data]))
//		} else if (status == txStatusOps.aborted) {
//
//
//			session.execute(
//				delete()
//					.from(keyspace.dataTable.name)
//					.where(QueryBuilder.eq("id", id))
//					.and(QueryBuilder.eq("key", key))
//				)
//
//			/*
//			Alternatively, one can set the transaction status to aborted. One have to change the reading accordingly.
//
//			session.execute(
//				update(keyspace.dataTable.name)
//				.`with`(set("txstatus", txStatusOps.committed))
//				.where(QueryBuilder.eq("id", id))
//				.and(QueryBuilder.eq("key", key))
//			)
//			*/
//
//			//Recursively read the next key
//			//TODO: Retry only for X times
//			//TODO: Recurse directly this method instead of calling the "parent method" read.
//			return read(session, key)
//		}
//
//		//We handled the 3 txstates pending, committed, and aborted. We should never get here.
//		//		assert(false, "unhandled transaction state: " + status)
//		return Error(key, new IllegalStateException("unhandled transaction state: " + status))
//	}
//
//
//}
