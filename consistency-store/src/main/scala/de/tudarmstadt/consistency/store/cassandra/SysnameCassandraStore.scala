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
	val keys : Keys[Key]
	val txStatuses : TxStatuses[TxStatus]
	val isolationLevels : IsolationLevels[Isolation]
	val consistencyLevels : ConsistencyLevels[Consistency]

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
			case l if l == isolationLevels.snapshotIsolation =>
				val txContext = new SysnameCassandraSnapshotIsolatedTxContext(params)
				executeBufferedTransaction(f, txContext, SnapshotIsolatedTransactions)

			case l if l == isolationLevels.readCommitted =>
				val txContext = new SysnameCassandraReadCommittedTxContext(params)
				executeBufferedTransaction(f, txContext, ReadCommittedTransactions)

			case l if l == isolationLevels.none =>
				val txContext = new SysnameCassandraNoneTxContext(params)
				executeNonIsolatedTransaction(f, txContext, ReadCommittedTransactions)

			case l =>
				throw new UnsupportedIsolationLevelException(l)
		}

		private def executeNonIsolatedTransaction[U](f : Transaction[U], txContext : CassandraTxContext, processor : TransactionProcessor) : Option[U] = {
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

		private def executeBufferedTransaction[U](f : Transaction[U], txContext : BufferedWritesCassandraTxContext, processor : TransactionProcessor) : Option[U] = {
			try {
				f(txContext) match {
					case None =>
						//if there has been a user initiated abort (i.e. f returned None), then abort the transaction
						return None

					case Some(result) =>

						//If the user wants to commit the transaction, then try to commit it.
						SnapshotIsolatedTransactions.commit(session, SysnameCassandraStore.this)(
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

			Log.info(null, s"read all versions. key = $key, result = $keyResult")


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
			case l if l == isolationLevels.snapshotIsolation =>
				assert(txParams.txid.isDefined, "snapshot isolated value needs to be accessed from a transaction with txid") //TODO: No it doesnt!
				SnapshotIsolatedTransactions.isRowCommitted(session, SysnameCassandraStore.this)(txParams.txid.get.id, row).isSuccess
			case l if l == isolationLevels.readCommitted =>
				assert(txParams.txid.isDefined, "read committed isolated value needs to be accessed from a transaction with txid") //TODO: No it doesnt!
				ReadCommittedTransactions.isRowCommitted(session, SysnameCassandraStore.this)(txParams.txid.get.id, row).isSuccess
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
					case upd@Update(_, updKey, _, _, _) =>
						assert(key == updKey, "inconsistent update: update key does not match key")
						update(upd, params)
					case tx : Tx[Id, Key, Data] =>
						assert(key == keys.transactionKey, "inconsistent update: key does not match default transaction key")
						update(tx, params)
				}
			}

			def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit
			def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit

		}

		trait BufferedWritesCassandraTxContext extends CassandraTxContext {
			private val updates : mutable.Buffer[WriteUpdate] = mutable.Buffer.empty
			private val tx : Array[WriteTx] = Array(null)

			def bufferUpdate(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				updates += WriteUpdate(SysnameCassandraStore.this)(update, params)
			}

			def bufferTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(getTx.isEmpty, "already buffered another transaction record for this transaction")
				this.tx(0) = WriteTx(SysnameCassandraStore.this)(tx, params)
			}

			def getTx : Option[WriteTx] =
				Option(tx(0))

			def getTxOrError : WriteTx = {
				if (tx(0) == null)
					throw new IllegalStateException("cannot commit transaction without txid: no tx record supplied")

				tx(0)
			}

			def getUpdates : Seq[WriteUpdate] = updates

			override def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit =
				bufferUpdate(update, params)

			override def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit =
				bufferTx(tx, params)
		}

		private class SysnameCassandraSnapshotIsolatedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraReadCommittedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraNoneTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(update.txid.isEmpty, "a transaction without isolation can not depend on a transaction record")

				val write = WriteUpdate(SysnameCassandraStore.this)(update, params)
				write.writeData(session, ConsistencyLevel.ONE)(txStatuses.committed, isolationLevels.none)
			}

			def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(assertion = false, "transaction with isolation level none cannot have a transaction record")
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
