package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core._
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.exceptions.UnsupportedIsolationLevelException
import de.tudarmstadt.consistency.store.shim.Event
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
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

	type CassandraSession = com.datastax.driver.core.Session

	override type SessionCtx = SysnameCassandraSessionContext

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


	protected var cluster : Cluster =
		connectionParams.connectCluster

	private [cassandra] val keyspace : KeyspaceDef =
		createKeyspaceDef


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

	override def close(): Unit = {
		cluster.close()
	}


	class SysnameCassandraSessionContext(val session : CassandraSession) extends SessionContext {

		type TxCtx = CassandraTxContext

		override def startTransaction[U](params : CassandraTxParams[Id, Isolation])(f : Transaction[U]) : Option[U] = params.isolation match {
				case l if l == isolationLevels.snapshotIsolation =>
					val txContext = new SysnameCassandraSnapshotIsolatedTxContext(params)
					f(txContext) match {
						case None => return None
						case result@Some(_) => SnapshotIsolatedTransactions.commit(session, SysnameCassandraStore.this)(
							txContext.getTxOrError, txContext.getUpdates
						) match {
							case CommitStatus.Success(_, _) => return result
							case CommitStatus.Abort(_, desc) =>
								Log.info(classOf[SysnameCassandraSessionContext], desc)
								return None
							case CommitStatus.Error(_, e) => throw e
						}
					}

				case l if l == isolationLevels.readCommitted =>
					val txContext = new SysnameCassandraReadCommittedTxContext(params)
					f(txContext) match {
						case None => return None
						case result@Some(_) => ReadCommittedTransactions.commit(session, SysnameCassandraStore.this)(
							txContext.getTxOrError, txContext.getUpdates
						) match {
							case CommitStatus.Success(_, _) => return result
							case CommitStatus.Abort(_, desc) =>
								Log.info(classOf[SysnameCassandraSessionContext], desc)
								return None
							case CommitStatus.Error(_, e) => throw e
						}
					}
		}

		private def readKey(key : Key, readParams : CassandraReadParams[Id, Consistency]) : Seq[Event[Id, Key, Data]] = {
			readParams match {
				case CassandraReadParams(Some(id), _) => readVersionOf(key, id).toSeq
				case CassandraReadParams(None, _) => readAllVersionsOf(key)
			}
		}


		private def readAllVersionsOf(key : Key) : Seq[Event[Id, Key, Data]] = {
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
				val dataRow : DataRow = CassandraRow(row)

				val rowIsCommitted = commitRow(dataRow)

				if (rowIsCommitted) {
					buf.prepend(dataRow.toEvent)
				}

				row = keyResult.one()
			}

			return buf
		}

		private def readVersionOf(key : Key, id : Id) : Option[Event[Id, Key, Data]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.dataTable.name)
					.where(QueryBuilder.eq("key", key))
  				.and(QueryBuilder.eq("id", id))
			)

			val row = keyResult.one()
			if (row == null) {
				return None
			}

			val dataRow : DataRow = CassandraRow(row)

			val rowIsCommitted = commitRow(dataRow)

			if (rowIsCommitted) {
				return Some(dataRow.toEvent)
			} else {
				return None
			}
		}

		private def commitRow(row : DataRow) : Boolean = row.isolation match {
			case l if l == isolationLevels.snapshotIsolation =>
				SnapshotIsolatedTransactions.commitRow(session, SysnameCassandraStore.this)(row)
			case l if l == isolationLevels.readCommitted =>
				ReadCommittedTransactions.commitRow(session, SysnameCassandraStore.this)(row)
			case iso => throw new UnsupportedIsolationLevelException(iso)
		}


		trait CassandraTxContext extends TxContext {
			override def read(key : Key, params : CassandraReadParams[Id, Consistency]) : Seq[Event[Id, Key, Data]] = {
				readKey(key, params)
			}


			override def update(key : Key, data : Event[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				data match {
					case upd@Update(_, updKey, _, _, _) =>
						assert(key == updKey, "inconsistent update: update key does not match key")
						update(upd, params)
					case tx : Tx[Id, Key, Data] =>
						assert(key == keys.transactionKey, "inconsistent tx: key does not match default transaction key")
						update(tx, params)
				}
			}

			def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit
			def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit

		}

		trait BufferedCassandraTxContext extends CassandraTxContext {
			private val updates : mutable.Buffer[WriteUpdate] = mutable.Buffer.empty
			private val tx : Array[WriteTx] = Array(null)

			def bufferUpdate(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				updates += WriteUpdate(update, params)
			}

			def bufferTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(getTx.isEmpty, "already buffered another transaction record for this transaction")
				this.tx(0) = WriteTx(tx, params)
			}

			def getTx : Option[WriteTx] =
				Option(tx(0))

			def getTxOrError : WriteTx = {
				if (tx(0) == null)
					throw new IllegalStateException("cannot commit transaction without txid: no tx record supplied")

				tx(0)
			}

			def getUpdates : Seq[WriteUpdate] =
				updates

			override def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit =
				bufferUpdate(update, params)

			override def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit =
				bufferTx(tx, params)
		}

		private class SysnameCassandraSnapshotIsolatedTxContext(val txParams : CassandraTxParams[Id, Isolation]) extends BufferedCassandraTxContext

		private class SysnameCassandraReadCommittedTxContext(val txParams : CassandraTxParams[Id, Isolation]) extends BufferedCassandraTxContext

		private class SysnameCassandraNoneTxContext(val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			def update(update : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(update.txid.isEmpty, "a transaction without isolation can not depend on a transaction record")

				try {
					WriteUpdate(update, params).writeData(session, ConsistencyLevel.ONE)(txStatuses.committed, isolationLevels.none)
				} catch {
					//TODO: Real error handling here
					case e : Exception => throw e
				}

			}

			def update(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) : Unit = {
				assert(assertion = false, "transaction with isolation level none cannot have a transaction record")
			}

		}


		@Deprecated
		def refresh() : ResultSet = {
			Fetcher.fetch(session)
		}


		object Fetcher {
			def fetch(session : CassandraSession) : ResultSet = {
				import com.datastax.driver.core.querybuilder.QueryBuilder._

				val results : ResultSet = session.execute(
					select().all().from(keyspace.dataTable.name)
				)

				results

			}


//			def fetchNewerThen(session : Session, id : Id) : Unit = {
//				import com.datastax.driver.core.querybuilder.QueryBuilder._
//
//				val results : ResultSet = session.execute(
//					select().all().from(store.keyspace.dataTable.name).where(gt("id", id))
//						//TODO: Remove performance bottleneck: allow filtering
//						.allowFiltering()
//				)
//
//				handleResultSet(results)
//			}
//
//
//			override def fetchForKey(session : Session, key : Key) : Unit = {
//				import com.datastax.driver.core.querybuilder.QueryBuilder._
//
//				val results : ResultSet = session.execute(
//					select().all().from(store.keyspace.dataTable.name).where(QueryBuilder.eq("key", key))
//				)
//
//				handleResultSet(results)
//			}
//
//
//			def fetchKeyNewerThen(session : Session, key : Key, id : Id) : Unit = {
//				import com.datastax.driver.core.querybuilder.QueryBuilder._
//
//				val results : ResultSet = session.execute(
//					select().all()
//						.from(store.keyspace.dataTable.name)
//						.where(QueryBuilder.eq("key", key))
//						.and(gt("id", id))
//				)
//
//				handleResultSet(results)
//			}
		}
		override def print() : Unit = ???
	}



	def initializeKeyspace(): Unit = {
		keyspace.initialize(cluster)
	}

	private [cassandra] def eventRefToCassandraTuple(ref : UpdateRef[Id, Key]) : TupleValue = {
		val typ = cluster.getMetadata.newTupleType(idType.getCqlType, keyType.getCqlType)
		typ.newValue(ref.id.asInstanceOf[AnyRef], ref.key.asInstanceOf[AnyRef])
	}

	private [cassandra] def dependencySetToCassandraSet(set : Set[UpdateRef[Id, Key]]) : java.util.Set[TupleValue] = {
		JavaConverters.setAsJavaSet(set.map(eventRefToCassandraTuple))
	}



	private[cassandra] def newSession : CassandraSession =
		cluster.connect(keyspace.name)

	/**
		* Defines the keyspace that is used for the store.
		*/
	private def createKeyspaceDef : KeyspaceDef = new KeyspaceDef {
		override val name : String = keyspaceName

		override protected def create(session : CassandraSession) : Unit = {
			//Strategy NetworkTopologyStrategy does not support a replication factor.
			//Initialize the keyspace
			session.execute(s"DROP KEYSPACE IF EXISTS $name;")
			session.execute(
				s"""CREATE KEYSPACE $name
					 | WITH replication = {'class': 'SimpleStrategy', 'replication_factor': 3 };""".stripMargin
			)

			//Use the keypsace as default keyspace
			session.execute(s"USE $name;")


			//Create aggregate function for reading most up-to-date row
			//tuple of (id, key, data, deps, txid, consistency)
//			val returnType = s"tuple<${cassandraTypeOf[Id]}, ${cassandraTypeOf[Key]}, ${cassandraTypeOf[Data]}, set<${cassandraTypeOf[Id]}>, ${cassandraTypeOf[Id]}, ${cassandraTypeOf[Consistency]}>"
//
//			//TODO: This function is currently not used. Remove it when decision was made to not use it...
//			session.execute(
//				s"""CREATE OR REPLACE FUNCTION biggerRow(
//					 |  max $returnType,
//					 |  id ${cassandraTypeOf[Id]}, key ${cassandraTypeOf[Key]}, data ${cassandraTypeOf[Data]}, deps set<${cassandraTypeOf[Id]}>, txid ${cassandraTypeOf[Id]}, consistency ${cassandraTypeOf[Consistency]})
//					 |		CALLED ON NULL INPUT
//					 |		RETURNS $returnType
//					 |		LANGUAGE java
//					 |		AS '$maxFunctionDef';
//			 """.stripMargin)
//
//
//			session.execute(
//				s"""CREATE OR REPLACE AGGREGATE maxRow($idType, $keyType, $dataType, set<$idType>, $idType, $consistencyLevelType)
//					 |SFUNC biggerRow
//					 |STYPE $returnType
//					 |INITCOND (null, null, null, null, null, null);
//					 |
//			 """.stripMargin
//			)
		}


		override val txTable : TableDef = new TableDef {
			override val name : String = "t_tx"
			override def create(session : CassandraSession) : Unit = session.execute(
					s"""CREATE TABLE $name
						 | (txid ${idType.getCqlType.asFunctionParameterString},
						 | status ${txStatusType.getCqlType.asFunctionParameterString},
						 | isolation ${isolationType.getCqlType.asFunctionParameterString},
						 | PRIMARY KEY(txid));""".stripMargin
				)
			}


		override val keyTable : TableDef = new TableDef {
			override val name : String = "t_keys"
			override def create(session : CassandraSession) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (key ${keyType.getCqlType.asFunctionParameterString},
					 | txid ${idType.getCqlType.asFunctionParameterString},
					 | PRIMARY KEY(key));""".stripMargin
			)
		}

		override val dataTable : TableDef = new TableDef {
			override val name : String = "t_data"
			override def create(session : CassandraSession) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (id ${idType.getCqlType.asFunctionParameterString()},
					 | key ${keyType.getCqlType.asFunctionParameterString},
					 | data ${dataType.getCqlType.asFunctionParameterString},
					 | deps set<frozen<tuple<${idType.getCqlType.asFunctionParameterString}, ${keyType.getCqlType.asFunctionParameterString}>>>,
					 | txid ${idType.getCqlType.asFunctionParameterString},
					 | txstatus ${txStatusType.getCqlType.asFunctionParameterString},
					 | consistency ${consistencyType.getCqlType.asFunctionParameterString},
					 | isolation ${isolationType.getCqlType.asFunctionParameterString},
					 | PRIMARY KEY (key, id));""".stripMargin
			)
		}
	}



	/**
		* Define a function body (as Java source) that is used to compute the more up-to-date
		* row of two given rows.
		* The parameters that are available are id, key, data, dependencies (as a set), txid, and consistency.
		* The types are as defined by the type factories.
		*/
//	protected val maxFunctionDef : String




	trait KeyspaceDef {
		/**
			* Name of this Cassandra keyspace.
			*/
		def name : String

		val txTable : TableDef
		val keyTable : TableDef
		val dataTable : TableDef

		/**
			* Creates a new keyspace in Cassandra. Does not initialize any tables.
			* @param session The session to the cluster where the keyspace should be initialized.
			*/
		protected def create(session : CassandraSession) : Unit

		def initialize(cluster : Cluster) : Unit = {
			val session = cluster.connect()
			create(session)

			session.execute(s"USE $name")

			txTable.create(session)
			keyTable.create(session)
			dataTable.create(session)

			session.close()
		}
	}

	trait TableDef {
		val name : String
		def create(session : CassandraSession)
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



	trait DataRow {
		def id : Id
		def key : Key
		def data : Data
		def txid : Option[TxRef[Id]]
		def deps : Set[UpdateRef[Id, Key]]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency

		def cassandraTxid : Any =
			txid.map(ref => ref.id).getOrElse(null)

		def toEvent : Event[Id, Key, Data] = {
			if (key == keys.transactionKey) {
				return Tx(id, deps)
			} else {
				return Update(id, key, data, txid, deps)
			}
		}


	}

	case class CassandraRow(row : Row) extends DataRow {
		override def id : Id = row.get("id", idType)
		override def key : Key = row.get("key", keyType)
		override def data : Data = row.get("data", dataType)
		override def txid : Option[TxRef[Id]] = Option(TxRef(row.get("txid", idType)))
		override def deps : Set[UpdateRef[Id, Key]] = {
			val rawSet : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[TupleValue])).toSet
			rawSet.map(tv => {
				val id = tv.get(0, idType)
				val key = tv.get(1, keyType)
				UpdateRef(id, key)
			})
		}
		override def txStatus : TxStatus = row.get("txstatus", txStatusType)
		override def isolation : Isolation = row.get("isolation", isolationType)
		override def consistency : Consistency = row.get("consistency", consistencyType)
	}

	case class LocalRow(id: Id, key: Key, data: Data, txid: Option[TxRef[Id]], deps: Set[UpdateRef[Id, Key]], txStatus: TxStatus, isolation: Isolation, consistency: Consistency)
		extends DataRow

	trait Write {
		def writeData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE)(txStatus : TxStatus, isolation : Isolation) : Unit
	}

	case class WriteUpdate(upd : Update[Id, Key, Data], params : CassandraWriteParams[Consistency]) extends Write {

		override def writeData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE)(txStatus : TxStatus, isolation : Isolation) : Unit = {

			val convertedTxid = upd.txid.map(ref => ref.id).getOrElse(null)
			val convertedDependencies : java.util.Set[TupleValue] = dependencySetToCassandraSet(upd.readDependencies)

			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				update(keyspace.dataTable.name)
					.`with`(set("data", upd.data))
					.and(set("deps", convertedDependencies))
					.and(set("txid", convertedTxid))
					.and(set("txstatus", txStatus))
					.and(set("isolation", isolation))
					.and(set("consistency", params.consistency))
					.where(QueryBuilder.eq("key", upd.key))
					.and(QueryBuilder.eq("id", upd.id))
					.setConsistencyLevel(writeConsistency)
			)
		}
	}

	case class WriteTx(tx : Tx[Id, Key, Data], params : CassandraWriteParams[Consistency]) extends Write {
		override def writeData(session : CassandraSession, writeConsistency : ConsistencyLevel)(txStatus : TxStatus, isolation : Isolation) : Unit = {
			val convertedDependencies : java.util.Set[TupleValue] = dependencySetToCassandraSet(tx.readDependencies)

			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				update(keyspace.dataTable.name)
					.`with`(set("data", null))
					.and(set("deps", convertedDependencies))
					.and(set("txid", tx.id))
					.and(set("txstatus", txStatus))
					.and(set("isolation", isolation))
					.and(set("consistency", params.consistency))
					.where(QueryBuilder.eq("key", keys.transactionKey))
					.and(QueryBuilder.eq("id", tx.id))
					.setConsistencyLevel(writeConsistency)
			)
		}
	}
}
