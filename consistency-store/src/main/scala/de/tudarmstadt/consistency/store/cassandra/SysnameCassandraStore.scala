package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core._
import com.datastax.driver.core.exceptions.QueryExecutionException
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.store.Store.AbortedException
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.Keyspaces.{KeyspaceDef, TableDef}
import de.tudarmstadt.consistency.store.cassandra.TransactionProcessor.{Abort, Success}
import de.tudarmstadt.consistency.store.cassandra.Writes.{WriteTx, WriteUpdate}
import de.tudarmstadt.consistency.store.cassandra.exceptions.UnsupportedIsolationLevelException
import de.tudarmstadt.consistency.store.shim.Event
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.utils.Log

import scala.collection.{JavaConverters, mutable}
import scala.reflect.runtime.universe._

/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
abstract class SysnameCassandraStore[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag]
	extends Store[
		Key,
		Event[Id, Key, Data],
		CassandraTxParams[Id, Isolation],
		CassandraWriteParams[Consistency],
		CassandraReadParams[Id, Consistency],
		Seq[Event[Id, Key, Data]]
		] {


	override type SessionCtx = SysnameCassandraSessionContext

	type DataRow = DataRows.DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]

	type WriteUpdate = Writes.WriteUpdate[Id, Key, Data, TxStatus, Isolation, Consistency]
	type WriteTx = Writes.WriteTx[Id, Key, Data, TxStatus, Isolation, Consistency]


	protected val connectionParams : ConnectionParams

	val keyspaceName : String

	val idType : TypeCodec[Id]
	val keyType : TypeCodec[Key]
	val dataType : TypeCodec[Data]
	val txStatusType : TypeCodec[TxStatus]
	val isolationType : TypeCodec[Isolation]
	val consistencyType : TypeCodec[Consistency]

	//	val idOps : IdOps[Id]
	val Keys : Keys[Key]
	val TxStatuses : TxStatuses[TxStatus]
	val IsolationLevels : IsolationLevels[Isolation]
	val ConsistencyLevels : ConsistencyLevels[Consistency]

	private [cassandra] val cluster : Cluster =
		connectionParams.connectCluster

	private [cassandra] val keyspace : KeyspaceDef =
		Keyspaces.createCassandraKeyspaceFor(this)


	override def startSession[U](f : Session[U]) : U = {
		val session = newSession
		val ctx = new SysnameCassandraSessionContext(session)

		try {
			val res = f(ctx)
			return res
		} finally {
			session.close()
		}
	}

	override def initialize(): Unit = {
		keyspace.initialize(cluster)
	}

	override def reset(): Unit = {
		keyspace.reset(cluster)
	}

	override def close(): Unit = {
		cluster.close()
	}


	private def newSession : CassandraSession =
		cluster.connect(keyspace.name)

	private [cassandra] def makeDataRow(row : Row) =
		DataRows.CassandraRow(this)(row)



	class SysnameCassandraSessionContext(val session : CassandraSession) extends SessionContext {

		type TxCtx = CassandraTxContext

		override def startTransaction[U](params : CassandraTxParams[Id, Isolation])(f : Transaction[U]) : Option[U] = params.isolation match {
			case IsolationLevels.NONE =>
				val txContext = new SysnameCassandraNoneTxContext(params)
				executeNonIsolatedTransaction(f, txContext)

			case IsolationLevels.RU =>
				val txContext = new SysnameCassandraReadUncommittedTxContext(params)
				executeRUTransaction(f, txContext, ReadUncommittedTransactions)

			case IsolationLevels.RC =>
				val txContext = new SysnameCassandraReadCommittedTxContext(params)
				executeBufferedTransaction(f, txContext, ReadCommittedTransactions)

			case IsolationLevels.SI =>
				val txContext = new SysnameCassandraSnapshotIsolatedTxContext(params)
				executeBufferedTransaction(f, txContext, SnapshotIsolatedTransactions)

			case l =>
				throw new UnsupportedIsolationLevelException(l)
		}

		private def executeNonIsolatedTransaction[U](f : Transaction[U], txContext : CassandraTxContext) : Option[U] = {
			try {
				f(txContext) match {
					case None =>
						throw new UnsupportedOperationException("none isolated transactions cannot be aborted")
					case opt@Some(_) =>
						opt
				}
			} catch {
				case e : QueryExecutionException =>
					//There was an error when either executing the transaction f or when committing the transaction
					//In both cases, abort the transaction
					Log.err(classOf[SysnameCassandraSessionContext], e.getMessage)
					return None
				case e : AbortedException =>
					throw new UnsupportedOperationException("none isolated tranasactions cannot be aborted", e)
			}
		}

		private def executeRUTransaction[U](f : Transaction[U], txContext : SysnameCassandraReadUncommittedTxContext, processor : TransactionProcessor) : Option[U] = {
			def abortWithHandling() : Unit = {
				try {
					txContext.undo()
				} catch {
					case e : QueryExecutionException =>
						e.printStackTrace()
						//TODO: Remove the assert -- we have to handle execption during undo accordingly
						assert(false, "query execution exception during undo")
				}
			}

			try {
				f(txContext) match {
					case None =>
						return None
					case opt@Some(_) =>
						processor.commit(session, SysnameCassandraStore.this)(
							txContext.getTxOrError, Set.empty
						) match {
							case Success =>
								return opt
							case Abort(msg) =>
								assert(false, "this case should never happen")
								txContext.undo()
								return None
						}
				}
			} catch {
				case e : QueryExecutionException =>
					Log.err(getClass, "system initiated abort of the transaction")
					abortWithHandling()
					return None
				case _ : AbortedException =>
					abortWithHandling()
					return None
			}
		}

		private def executeBufferedTransaction[U](f : Transaction[U], txContext : BufferedWritesCassandraTxContext, processor : TransactionProcessor) : Option[U] = {
			try {
				f(txContext) match {
					case None =>
						//if there has been a user initiated abort (i.e. f returned None), then abort the transaction
						return None

					case Some(result) =>

						//If the user wants to commit the transaction, then try to commit it.
						processor.commit(session, SysnameCassandraStore.this)(
							txContext.getTxOrError, txContext.getUpdates
						) match {
							case Success =>
								//The transaction has been successfully committed
								return Some(result)
							case Abort(msg) =>
								//There was a failure when committing the transaction => Abort
								Log.err(classOf[SysnameCassandraSessionContext], msg)
								return None
						}
				}
			} catch {
				case e : QueryExecutionException =>
					//There was an error when either executing the transaction f or when committing the transaction
					//In both cases, abort the transaction
					Log.err(classOf[SysnameCassandraSessionContext], e.getMessage)
					return None
				case e : AbortedException =>
					return None
			}
		}

		private def readKey(key : Key, readParams : CassandraReadParams[Id, Consistency], txParams : CassandraTxParams[Id, Isolation]) : Seq[Event[Id, Key, Data]] = {
			readParams match {
				case CassandraReadParams(Some(id), _) => readVersionOf(key, id, txParams).toSeq
				case CassandraReadParams(None, _) => readAllVersionsOf(key, txParams)
			}
		}


		private def readAllVersionsOf(key : Key, txParams : CassandraTxParams[Id, Isolation]) : Seq[Event[Id, Key, Data]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.dataTable.name)
  				.where(QueryBuilder.eq("key", key))
			)

			val buf : mutable.Buffer[Event[Id, Key, Data]] = mutable.Buffer.empty

			//Iterate through all rows of the result
			var row = keyResult.one()
			while (row != null) {
				val dataRow : DataRow = makeDataRow(row)

				val rowIsCommitted = commitRow(dataRow, txParams)

				if (rowIsCommitted) {
					buf.prepend(dataRow.toEvent)
				}

				row = keyResult.one()
			}

			return buf
		}

		private def readVersionOf(key : Key, id : Id, txParams : CassandraTxParams[Id, Isolation]) : Option[Event[Id, Key, Data]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.dataTable.name)
					.where(QueryBuilder.eq("key", key))
  				.and(QueryBuilder.eq("id", id))
			)

			val row = keyResult.one()

			Log.info(null, s"read version. key = $key, id = $id, result = $keyResult")

			if (row == null) {
				return None
			}

			val dataRow : DataRow = makeDataRow(row)

			val rowIsCommitted = commitRow(dataRow, txParams)

			if (rowIsCommitted) {
				return Some(dataRow.toEvent)
			} else {
				return None
			}
		}

		private def commitRow(row : DataRow, txParams : CassandraTxParams[Id, Isolation]) : Boolean = row.isolation match {
			case IsolationLevels.SI =>
				SnapshotIsolatedTransactions.isRowCommitted(session, SysnameCassandraStore.this)(txParams.txid.map(ref => ref.id), row).isSuccess
			case IsolationLevels.RU =>
				ReadUncommittedTransactions.isRowCommitted(session, SysnameCassandraStore.this)(txParams.txid.map(ref => ref.id), row).isSuccess
			case IsolationLevels.RC =>
				ReadCommittedTransactions.isRowCommitted(session, SysnameCassandraStore.this)(txParams.txid.map(ref => ref.id), row).isSuccess
			case IsolationLevels.NONE =>
				true
			case iso =>
				throw new UnsupportedIsolationLevelException(iso)
		}


		trait CassandraTxContext extends TxContext {
			val txParams : CassandraTxParams[Id, Isolation]

			override def read(key : Key, params : CassandraReadParams[Id, Consistency]) : Seq[Event[Id, Key, Data]] = {
				readKey(key, params, txParams)
			}

			override def write(key : Key, data : Event[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				data match {
					case upd@Update(_, updKey, _, updTxid, _) =>
						assert(key == updKey, "inconsistent update: update key does not match key")
						assert(updTxid == txParams.txid, "inconsistent update: the txid of the update and the tx have to match")

						write(upd, params)
					case tx : Tx[Id, Key, Data] =>
						assert(key == Keys.transactionKey, "inconsistent update: key does not match default transaction key")
						write(tx, params)
				}
			}

			def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate
			def write(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx

		}

		trait BufferedWritesCassandraTxContext extends CassandraTxContext {
			private val updates : mutable.Buffer[WriteUpdate] = mutable.Buffer.empty
			private val tx : Array[WriteTx] = Array(null)

			def bufferUpdate(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				val res = new WriteUpdate(SysnameCassandraStore.this)(update, params)
				updates += res
				res
			}

			def bufferTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx = {
				assert(getTx.isEmpty, "already buffered another transaction record for this transaction")
				assert(tx.id == txParams.txid.get.id, "the txid of the tx record has to be the same as the txid given by the parameter")
				val res = new WriteTx(SysnameCassandraStore.this)(tx, params)
				this.tx(0) = res
				res
			}

			def getTx : Option[WriteTx] =
				Option(tx(0))

			def getTxOrError : WriteTx = {
				if (tx(0) == null)
					throw new IllegalStateException("cannot commit transaction without txid: no tx record supplied")

				tx(0)
			}

			def getUpdates : Seq[WriteUpdate] = updates

			override def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate =
				bufferUpdate(update, params)

			override def write(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx =
				bufferTx(tx, params)
		}


		private class SysnameCassandraSnapshotIsolatedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraReadCommittedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraReadUncommittedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext {

			override def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				val write = super.write(update, params)
				write.writeData(session, ConsistencyLevel.ONE)(TxStatuses.COMMITTED, IsolationLevels.NONE)
				write
			}

			override def write(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx = {
				val write = super.write(tx, params)
				write
			}

			private[cassandra] def undo(): Unit = {
				getUpdates.foreach(upd => upd.deleteData(session, ConsistencyLevel.ONE))
				getTx.foreach(tx => tx.deleteData(session, ConsistencyLevel.ONE))
			}
		}

		private class SysnameCassandraNoneTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				assert(update.txid.isEmpty, "a transaction without isolation can not depend on a transaction record")

				val write = new WriteUpdate(SysnameCassandraStore.this)(update, params)
				write.writeData(session, ConsistencyLevel.ONE)(TxStatuses.COMMITTED, IsolationLevels.NONE)
				write
			}

			def write(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx = {
				throw new UnsupportedOperationException("transaction with isolation level none cannot have a transaction record")
			}
		}


		override def print() : Unit = ???
	}

	/* temporary for debugging */
	def printTables(session : CassandraSession): Unit = {
		val r1 = session.execute("SELECT * FROM t_tx")
		Log.info(null, "t_tx")
		r1.forEach(row => Log.info(null, row))

		val r2 = session.execute("SELECT * FROM t_keys")
		Log.info(null, "t_keys")
		r2.forEach(row => Log.info(null, row))

		val r3 = session.execute("SELECT * FROM t_data")
		Log.info(null, "t_data")
		r3.forEach(row => Log.info(null, row))
	}




}
