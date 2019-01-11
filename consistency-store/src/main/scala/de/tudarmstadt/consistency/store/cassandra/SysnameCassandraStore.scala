package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core._
import com.datastax.driver.core.exceptions.QueryExecutionException
import com.datastax.driver.core.querybuilder.QueryBuilder
import com.google.common.util.concurrent.ListenableFuture
import de.tudarmstadt.consistency.store.Store.AbortedException
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.Keyspaces.KeyspaceDef
import de.tudarmstadt.consistency.store.cassandra.TransactionProcessor.{Abort, Success}
import de.tudarmstadt.consistency.storelayer.local.exceptions.UnsupportedIsolationLevelException
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.utils.Log

import scala.collection.mutable
import scala.reflect.runtime.universe._

/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
abstract class SysnameCassandraStore[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag]
	extends Store[
		Key,
		Update[Id, Key, Data],
		CassandraTxParams[Id, Isolation],
		CassandraWriteParams[Consistency],
		CassandraReadParams[Id, Consistency],
		Seq[Update[Id, Key, Data]]
		] {


	override type SessionCtx = SysnameCassandraSessionContext

	type ReadUpdate = Reads.ReadUpdate[Id, Key, Data, TxStatus, Isolation, Consistency]
	type ReadTx = Reads.ReadTx[Id, Key, Data, TxStatus, Isolation, Consistency]

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
	val TxStatuses : TxStatuses[TxStatus]
	val IsolationLevels : IsolationLevels[Isolation]
	val ConsistencyLevels : ConsistencyLevels[Consistency]

	private [cassandra] val cluster : Cluster =
		connectionParams.connectCluster

	private [cassandra] val keyspace : KeyspaceDef =
		Keyspaces.createCassandraKeyspaceFor(this)


	override def startSession[U](f : Session[U]) : U = {
		val session = newSession
		val ctx = new SysnameCassandraSessionContext(new DebugSession(session))

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

	private[cassandra] def makeUpdateRow(row : Row) =
		Reads.CassandraReadUpdate(this)(row)

	private[cassandra] def makeTxRow(row : Row) =
		Reads.CassandraReadTx(this)(row)



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
						processor.commitWrites(session, SysnameCassandraStore.this)(
							txContext.getTx.get, Set.empty
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
						processor.commitWrites(session, SysnameCassandraStore.this)(
							txContext.getTx.get, txContext.getUpdates
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

		private def readKey(key : Key, readParams : CassandraReadParams[Id, Consistency], txParams : CassandraTxParams[Id, Isolation]) : Seq[Update[Id, Key, Data]] = {
			readParams match {
				case CassandraReadParams(Some(id), _) => readVersionOf(key, id, txParams).toSeq
				case CassandraReadParams(None, _) => readAllVersionsOf(key, txParams)
			}
		}


		private def readAllVersionsOf(key : Key, txParams : CassandraTxParams[Id, Isolation]) : Seq[Update[Id, Key, Data]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.updateDataTable.name)
  				.where(QueryBuilder.eq("key", key))
			)

			val buf : mutable.Buffer[Update[Id, Key, Data]] = mutable.Buffer.empty

			//Iterate through all rows of the result
			var row = keyResult.one()
			while (row != null) {
				val dataRow : ReadUpdate = makeUpdateRow(row)

				val rowIsCommitted = readIsObservable(dataRow, txParams)

				if (rowIsCommitted) {
					buf.prepend(dataRow.toEvent)
				}

				row = keyResult.one()
			}

			Log.info(this.getClass, s"session: $session. read all versions of $key: $buf")

			return buf
		}

		private def readVersionOf(key : Key, id : Id, txParams : CassandraTxParams[Id, Isolation]) : Option[Update[Id, Key, Data]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.updateDataTable.name)
					.where(QueryBuilder.eq("key", key))
  				.and(QueryBuilder.eq("id", id))
			)

			val row = keyResult.one()

			if (row == null) {
				return None
			}

			val dataRow : ReadUpdate = makeUpdateRow(row)

			val rowIsCommitted = readIsObservable(dataRow, txParams)

			if (rowIsCommitted) {
				return Some(dataRow.toEvent)
			} else {
				return None
			}
		}

//		private def readTx(txid : Id) : Option[Tx[Id, Key, Data]] = {
//			import com.datastax.driver.core.querybuilder.QueryBuilder._
//
//			//Retrieve the history of a key.
//			val keyResult = session.execute(
//				select.all.from(keyspace.txDataTable.name)
//					.where(QueryBuilder.eq("id", txid))
//			)
//
//			val row = keyResult.one()
//
//			if (row == null) {
//				return None
//			}
//
//			val dataRow : ReadUpdate = makeUpdateRow(row)
//
//			val rowIsCommitted = readIsObservable(dataRow, )
//
//			if (rowIsCommitted) {
//				return Some(dataRow.toEvent)
//			} else {
//				return None
//			}
//		}

		private def readIsObservable(row : ReadUpdate, txParams : CassandraTxParams[Id, Isolation]) : Boolean = row.isolation match {
			case IsolationLevels.SI =>
				SnapshotIsolatedTransactions.readIsObservable(session, SysnameCassandraStore.this)(txParams.id, row).isSuccess
			case IsolationLevels.RU =>
				ReadUncommittedTransactions.readIsObservable(session, SysnameCassandraStore.this)(txParams.id, row).isSuccess
			case IsolationLevels.RC =>
				ReadCommittedTransactions.readIsObservable(session, SysnameCassandraStore.this)(txParams.id, row).isSuccess
			case IsolationLevels.NONE =>
				true
			case iso =>
				throw new UnsupportedIsolationLevelException(iso)
		}


		trait CassandraTxContext extends TxContext {
			val txParams : CassandraTxParams[Id, Isolation]

			override def read(key : Key, params : CassandraReadParams[Id, Consistency]) : Seq[Update[Id, Key, Data]] = {
				readKey(key, params, txParams)
			}

			override def write(key : Key, data : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				data match {
					case upd@Update(_, updKey, _, updTxid, _) =>
						assert(key == updKey, "inconsistent update: update key does not match key")
						//assert(updTxid. == txParams.id), "inconsistent update: the txid of the update and the tx have to match")

						write(upd, params)
//					case tx : Tx[Id, Key, Data] =>
//						assert(key == Keys.TX_KEY, "inconsistent update: key does not match default transaction key")
//						write(tx, params)
				}
			}

			def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate
			def writeTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx
		}

		trait BufferedWritesCassandraTxContext extends CassandraTxContext {
			private val updates : mutable.Buffer[WriteUpdate] = mutable.Buffer.empty
			private var tx : WriteTx = null

			def bufferUpdate(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				val res = new WriteUpdate(SysnameCassandraStore.this)(update, params)
				updates += res
				res
			}

			def bufferTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx = {
				val res = new WriteTx(SysnameCassandraStore.this)(tx, params)
				this.tx = res
				res
			}

			def getTx : Option[WriteTx] = Option(tx)

			def getUpdates : Seq[WriteUpdate] = updates

			override def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate =
				bufferUpdate(update, params)

			override def writeTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx =
				bufferTx(tx, params)

		}


		private class SysnameCassandraSnapshotIsolatedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraReadCommittedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext

		private class SysnameCassandraReadUncommittedTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends BufferedWritesCassandraTxContext {

			override def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				val write = super.write(update, params)
				write.writeData(session, ConsistencyLevel.ONE)(TxStatuses.COMMITTED, IsolationLevels.RU)
				write
			}

			private[cassandra] def undo(): Unit = {
				getUpdates.foreach(upd => upd.deleteData(session, ConsistencyLevel.ONE))
			}

		}

		private class SysnameCassandraNoneTxContext(override val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			override def write(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteUpdate = {
				assert(update.txid.isEmpty, "a transaction without isolation can not depend on a transaction record")

				val write = new WriteUpdate(SysnameCassandraStore.this)(update, params)
				write.writeData(session, ConsistencyLevel.ONE)(TxStatuses.COMMITTED, IsolationLevels.NONE)
				write
			}

			override def writeTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : WriteTx = {
				throw new UnsupportedOperationException("cannot write tx in none isolated transaction")
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


	class DebugSession(val baseSession : CassandraSession) extends com.datastax.driver.core.Session {
		override def getLoggedKeyspace : String = baseSession.getLoggedKeyspace
		override def init() : CassandraSession = baseSession.init()
		override def initAsync() : ListenableFuture[CassandraSession] = baseSession.initAsync()
		override def execute(query : String) : ResultSet = {
			printExec(query)
			baseSession.execute(query)
		}
		override def execute(query : String, values : AnyRef*) : ResultSet = {
			printExec(query)
			baseSession.execute(query, values : _*)
		}
		override def execute(query : String, values : java.util.Map[String, AnyRef]) : ResultSet = {
			printExec(query)
			baseSession.execute(query, values)
		}
		override def execute(statement : Statement) : ResultSet = {
			printExec(statement)
			baseSession.execute(statement)
		}
		override def executeAsync(query : String) : ResultSetFuture = ???
		override def executeAsync(query : String, values : AnyRef*) : ResultSetFuture = ???
		override def executeAsync(query : String, values : java.util.Map[String, AnyRef]) : ResultSetFuture = ???
		override def executeAsync(statement : Statement) : ResultSetFuture = ???
		override def prepare(query : String) : PreparedStatement = ???
		override def prepare(statement : RegularStatement) : PreparedStatement = ???
		override def prepareAsync(query : String) : ListenableFuture[PreparedStatement] = {
			printPrepared(query)
			baseSession.prepareAsync(query)
		}
		override def prepareAsync(statement : RegularStatement) : ListenableFuture[PreparedStatement] = {
			printPrepared(statement)
			baseSession.prepareAsync(statement)
		}
		override def closeAsync() : CloseFuture = baseSession.closeAsync()
		override def close() : Unit = baseSession.close()
		override def isClosed : Boolean = baseSession.isClosed
		override def getCluster : Cluster = baseSession.getCluster
		override def getState : Session.State = baseSession.getState

		private def print(prefix : String, m : => Any) : Unit = {
			Log.info(classOf[DebugSession], s"[$baseSession] $prefix : ${m.toString}")
		}

		private def printPrepared(m : => Any) : Unit = {
			print("prepare stmt", m)
		}

		private def printExec(m : => Any) : Unit = {
			print("execute stmt", m)
		}
	}




}
