package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core._
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.shim.Event.EventRef
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
		Data,
		ResultSet,
		CassandraTxParams[Id, Isolation],
		CassandraWriteParams[Id, Key, Consistency],
		CassandraReadParams[Consistency],
		Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]]
		] {

	type CassandraSession = com.datastax.driver.core.Session

	type DepSet = Set[EventRef[Id, Key]]

	override type SessionCtx = SysnameCassandraSessionContext


	protected val connectionParams : ConnectionParams

	protected var cluster : Cluster =
		connectionParams.connectCluster

	val keyspace : KeyspaceDef =
		createKeyspaceDef


//	val idOps : IdOps[Id]
	val keyOps : KeyOps[Key]
	val txStatusOps : TxStatusOps[TxStatus]
	val isolationLevelOps : IsolationLevelOps[Isolation]
	val consistencyLevelOps : ConsistencyLevelOps[Consistency]


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

		override def startTransaction[U](params : CassandraTxParams[Id, Isolation])(f : Transaction[U]) : Option[U] = {
			val isolation = params.isolation
			val txid = params.txid

			isolation match {
				case l if l == isolationLevelOps.snapshotIsolation =>
					val txCtx = new SysnameCassandraSnapshotIsolatedTxContext(params)
					f(txCtx) match {
						case None =>
							return None
						case Some(u) =>
							SnapshotIsolatedTransactions.commit(session, SysnameCassandraStore.this)(txid, txCtx.updates.toSet, u) match {
								case CommitStatus.Success(_, _, result) =>
									return Some(result)
								case CommitStatus.Abort(_, desc) =>
									Log.info(classOf[SysnameCassandraSessionContext], desc)
									return None
								case CommitStatus.Error(_, e) =>
									throw e
							}
					}

				case l if l == isolationLevelOps.readCommitted =>
					val txCtx = new SysnameCassandraReadCommittedTxContext(params)
					f(txCtx) match {
						case None =>
							return None
						case Some(u) =>
							ReadCommittedTransactions.commit(session, SysnameCassandraStore.this)(txid, txCtx.updates.toSet, u) match {
								case CommitStatus.Success(_, _, result) =>
									return Some(result)
								case CommitStatus.Abort(_, desc) =>
									Log.info(classOf[SysnameCassandraSessionContext], desc)
									return None
								case CommitStatus.Error(_, e) =>
									throw e
							}
					}
			}
		}


		private def readHistoryOf(key : Key, txParams : CassandraTxParams[Id, Isolation], opParams : CassandraReadParams[Consistency]) : Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]] = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._

			//Retrieve the history of a key.
			val keyResult = session.execute(
				select.all.from(keyspace.dataTable.name)
  				.where(QueryBuilder.eq("key", key))
			)

			val buf : mutable.Buffer[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]] = mutable.Buffer.empty

			//Iterate through all rows of the result
			var row = keyResult.one()
			while (row != null) {
				val dataRow : DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] = CassandraRow(row)

				val rowIsCommitted = dataRow.isolation match {
					case l if l == isolationLevelOps.snapshotIsolation =>
						SnapshotIsolatedTransactions.commitRow(session, SysnameCassandraStore.this)(dataRow)
					case l if l == isolationLevelOps.readCommitted =>
						ReadCommittedTransactions.commitRow(session, SysnameCassandraStore.this)(dataRow)
				}

				if (rowIsCommitted) {
					buf.prepend(dataRow)
				}

				row = keyResult.one()
			}

			return buf
		}



		trait CassandraTxContext extends TxContext {

			//def readId(id : Id, key : Key, params : CassandraReadParams[Consistency])
		}


		private class SysnameCassandraSnapshotIsolatedTxContext(val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			type Update = CassandraUpdate[Id, Key, Data]

			val updates : mutable.Set[Update] = mutable.HashSet.empty

			override def update(key : Key, data : Data, params : CassandraWriteParams[Id, Key, Consistency]) : Unit = {
				updates.add(CassandraUpdate(params.id, key, data, params.deps))
			}

			override def read(key : Key, params : CassandraReadParams[Consistency]) : Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]] = {
				readHistoryOf(key, txParams, params)
			}
		}


		private class SysnameCassandraReadCommittedTxContext(val txParams : CassandraTxParams[Id, Isolation]) extends CassandraTxContext {

			type Update = CassandraUpdate[Id, Key, Data]

			val updates : mutable.Set[Update] = mutable.HashSet.empty

			override def update(key : Key, data : Data, params : CassandraWriteParams[Id, Key, Consistency]) : Unit = {
				updates.add(CassandraUpdate(params.id, key, data, params.deps))
			}

			override def read(key : Key, params : CassandraReadParams[Consistency]) : Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]] = {
				readHistoryOf(key, txParams, params)
			}
		}

		private class SysnameCassandraNoneTxContext(val txParams : CassandraTxParams[Id, Isolation], val txid : Id) extends CassandraTxContext {

			type Update = CassandraUpdate[Id, Key, Data]


			override def update(key : Key, data : Data, params : CassandraWriteParams[Id, Key, Consistency]) : Unit = {
				val CassandraWriteParams(id, deps, consistency) = params

				try {
					writeData(session, ConsistencyLevel.ONE)(
						id, key, data, deps, txid, txStatusOps.committed, consistency, isolationLevelOps.none
					)
				} catch {
					//TODO: Real error handling here
					case e : Exception => throw e
				}

			}

			override def read(key : Key, params : CassandraReadParams[Consistency]) : Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]] = {
				readHistoryOf(key, txParams, params)
			}
		}


		override def refresh() : ResultSet = {
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

	private [cassandra] def eventRefToCassandraTuple(ref : EventRef[Id, Key]) : TupleValue = {
		val typ = cluster.getMetadata.newTupleType(cassandraTypeOf[Id], cassandraTypeOf[Key])
		typ.newValue(ref.id.asInstanceOf[AnyRef], ref.key.asInstanceOf[AnyRef])
	}

	private [cassandra] def dependencySetToCassandraSet(set : Set[EventRef[Id, Key]]) : java.util.Set[TupleValue] = {
		JavaConverters.setAsJavaSet(set.map(eventRefToCassandraTuple))
	}

	private[cassandra] def writeData
	(
		session : CassandraSession, writeConsistency : ConsistencyLevel = ConsistencyLevel.ONE
	)(
		id : Id, key : Key, data : Data, deps : Set[EventRef[Id, Key]], txid : Id, txStatus : TxStatus, consistency : Consistency, isolation : Isolation
	) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val writeDepsJava : java.util.Set[TupleValue] = dependencySetToCassandraSet(deps)

		session.execute(
			update(keyspace.dataTable.name)
				.`with`(set("data", data))
				.and(set("deps", writeDepsJava))
				.and(set("txid", txid))
				.and(set("txstatus", txStatus))
				.and(set("consistency", consistency))
				.and(set("isolation", isolation))
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
				.setConsistencyLevel(writeConsistency)
		)
	}


	private[cassandra] def writeNullData
	(
		session : CassandraSession, writeConsistency : ConsistencyLevel = ConsistencyLevel.ONE
	)(
		id : Id, key : Key, deps : Set[EventRef[Id, Key]], txid : Id, txStatus : TxStatus, consistency : Consistency, isolation : Isolation
	) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val writeDepsJava : java.util.Set[TupleValue] = dependencySetToCassandraSet(deps)

		session.execute(
			update(keyspace.dataTable.name)
				.`with`(set("data", null))
				.and(set("deps", writeDepsJava))
				.and(set("txid", txid))
				.and(set("txstatus", txStatus))
				.and(set("consistency", consistency))
				.and(set("isolation", isolation))
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
				.setConsistencyLevel(writeConsistency)
		)
	}

	private[cassandra] def newSession : CassandraSession =
		cluster.connect(keyspace.name)

	/**
		* Defines the keyspace that is used for the store.
		*/
	private def createKeyspaceDef : KeyspaceDef = new KeyspaceDef {
		override val name : String = "k_sysname"

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
					 | (txid ${cassandraTypeOf[Id]},
					 | status ${cassandraTypeOf[TxStatus]},
					 | isolation ${cassandraTypeOf[Isolation]},
					 | PRIMARY KEY(txid));""".stripMargin
			)
		}

		override val keyTable : TableDef = new TableDef {
			override val name : String = "t_keys"
			override def create(session : CassandraSession) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (key ${cassandraTypeOf[Key]},
					 | txid ${cassandraTypeOf[Id]},
					 | PRIMARY KEY(key));""".stripMargin
			)
		}

		override val dataTable : TableDef = new TableDef {
			override val name : String = "t_data"
			override def create(session : CassandraSession) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (id ${cassandraTypeOf[Id]},
					 | key ${cassandraTypeOf[Key]},
					 | data ${cassandraTypeOf[Data]},
					 | deps set<frozen<tuple<${cassandraTypeOf[Id]}, ${cassandraTypeOf[Key]}>>>,
					 | txid ${cassandraTypeOf[Id]},
					 | txstatus ${cassandraTypeOf[TxStatus]},
					 | consistency ${cassandraTypeOf[Consistency]},
					 | isolation ${cassandraTypeOf[Isolation]},
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


}
