package de.tudarmstadt.consistency.store.scala.extra.internalstore

import java.util.UUID

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.querybuilder.QueryBuilder.{select, set, update}
import com.datastax.driver.core._
import de.tudarmstadt.consistency.store.scala.extra.StoreInterface
import de.tudarmstadt.consistency.store.scala.extra.Util._
import de.tudarmstadt.consistency.store.scala.extra._
import de.tudarmstadt.consistency.store.scala.extra.internalstore.exceptions.UnsupportedIsolationLevelException
import de.tudarmstadt.consistency.utils.Log

import scala.collection.{JavaConverters, mutable}
import scala.reflect.runtime.universe._

/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
abstract class SysnameCassandraStore[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag] extends StoreInterface[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraOpParams[Id, Consistency]] {

	type CassandraSession = com.datastax.driver.core.Session


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


	def startSession[U](f : SessionContext => U) : U = {
		val session = newSession
		val ctx = new SysnameCassandraSessionContext(session)

		try {
			val res = f(ctx)
			return res
		} finally {
			session.close()
		}
	}


	class SysnameCassandraSessionContext(val session : CassandraSession) extends SessionContext {

		override def startTransaction[U](params : CassandraTxParams[Id, Isolation])(f : TxContext => Option[U]) : Option[U] = {
			val isolation = params.isolation
			val txid = params.txid

			isolation match {
				case l if l == isolationLevelOps.snapshotIsolation =>
					val txCtx = new SysnameCassandraSnapshotIsolatedTxContext
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
					val txCtx = new SysnameCassandraReadCommittedTxContext
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







		private class SysnameCassandraSnapshotIsolatedTxContext extends TxContext {

			type Update = CassandraUpdate[Id, Key, Data]

			val updates : mutable.Set[Update] = mutable.HashSet.empty

			override def update(key : Key, data : Data, params : CassandraOpParams[Id, Consistency]) : Unit = {
				updates.add(CassandraUpdate(params.id, key, data, params.deps))
			}

			override def read(key : Key, params : CassandraOpParams[Id, Consistency]) : Option[Data] = {
				SnapshotIsolatedTransactions.read(session, SysnameCassandraStore.this)(key) match {
					case ReadStatus.Success(_, id, data, deps) =>
						return Some(data)
					case ReadStatus.NotFound(_, desc) =>
						Log.info(classOf[SysnameCassandraSnapshotIsolatedTxContext], desc)
						return None
					case ReadStatus.Error(_, e) =>
						throw e
				}
			}
		}


		private class SysnameCassandraReadCommittedTxContext extends TxContext {

			type Update = CassandraUpdate[Id, Key, Data]

			val updates : mutable.Set[Update] = mutable.HashSet.empty

			override def update(key : Key, data : Data, params : CassandraOpParams[Id, Consistency]) : Unit = {
				updates.add(CassandraUpdate(params.id, key, data, params.deps))
			}

			override def read(key : Key, params : CassandraOpParams[Id, Consistency]) : Option[Data] = {
				ReadCommittedTransactions.read(session, SysnameCassandraStore.this)(key) match {
					case ReadStatus.Success(_, id, data, deps) =>
						return Some(data)
					case ReadStatus.NotFound(_, desc) =>
						Log.info(classOf[SysnameCassandraSnapshotIsolatedTxContext], desc)
						return None
					case ReadStatus.Error(_, e) =>
						throw e
				}
			}
		}

		private class SysnameCassandraNoneTxContext(val txid : Id) extends TxContext {

			type Update = CassandraUpdate[Id, Key, Data]


			override def update(key : Key, data : Data, params : CassandraOpParams[Id, Consistency]) : Unit = {
				val CassandraOpParams(id, deps, consistency) = params

				try {
					writeData(session, ConsistencyLevel.ONE)(
						id, key, data, deps, txid, txStatusOps.committed, consistency, isolationLevelOps.none
					)
				} catch {
					//TODO: Real error handling here
					case e : Exception => throw e
				}

			}

			override def read(key : Key, params : CassandraOpParams[Id, Consistency]) : Option[Data] = {
				???
			}
		}


		override def update() : ResultSet = {
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



//	override def commit[Return](session : CassandraSession, transaction : Transaction[Return], isolation : Isolation)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return] =
//		throw new UnsupportedIsolationLevelException(isolation)
//
//
//
//	override def read(session : CassandraSession, key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : ReadStatus[Id, Key, Data] = {
//		import ReadStatus._
//
//		//Retrieve the maximum id for a given key
//		val maxResult = session.execute(select().max("id")
//			.from(keyspace.dataTable.name)
//			.where(QueryBuilder.eq("key", key))
//		)
//
//		val maxRow = maxResult.one()
//
//		if (maxRow == null) {
//			//			assert(false, "did not retrieve anything from database")
//			return NotFound(key, s"no entry for $key in database")
//		}
//
//
//		val readId = maxRow.get("system.max(id)", runtimeClassOf[Id])
//
//		if (readId == null) {
//			//			assert(false, "no rows left for key " + key)
//			return NotFound(key, s"no entry for $key in database")
//		}
//
//		//Retrieve the row with the maximum id
//		val readResult = session.execute(select().all()
//			.from(keyspace.dataTable.name)
//			.where(QueryBuilder.eq("id", readId))
//			.and(QueryBuilder.eq("key", key))
//		)
//
//		/*TODO: Another possibility would be to use the user defined maxRow which returns the complete row (in the aggregation) instead of just one column.
//
//		I have to make weigh the differences between these to possibilities.
//
//		select maxRow(id, key, data, deps, txid, consistency) from t_data where key = 'x';
//
//		 */
//
//		val readRow = readResult.one()
//
//		if (readRow == null) {
//			//			assert(false, "did not retrieve anything from database")
//			return NotFound(key, s"no entry for $key in database anymore (it may have been removed concurrently)")
//			//TODO: Retry here???
//		}
//
//		val isolation = readRow.get("isolation", runtimeClassOf[Isolation])
//
//		internalRead(session, readId, key, isolation, readRow)
//	}
//
//	protected def internalRead(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]): ReadStatus[Id, Key, Data] =
//		throw new UnsupportedIsolationLevelException(isolation)


	def initializeKeyspace(): Unit = {
		keyspace.initialize(cluster)
	}

	private[internalstore] def writeData
	(
		session : CassandraSession, writeConsistency : ConsistencyLevel = ConsistencyLevel.ONE
	)(
		id : Id, key : Key, data : Data, deps : Set[Id], txid : Id, txStatus : TxStatus, consistency : Consistency, isolation : Isolation
	) : Unit = {
		val writeDepsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(deps)

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


	private[internalstore] def writeNullData
	(
		session : CassandraSession, writeConsistency : ConsistencyLevel = ConsistencyLevel.ONE
	)(
		id : Id, key : Key, deps : Set[Id], txid : Id, txStatus : TxStatus, consistency : Consistency, isolation : Isolation
	) : Unit = {
		val writeDepsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(deps)

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

	private[internalstore] def newSession : CassandraSession =
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
					 | deps set<${cassandraTypeOf[Id]}>,
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


	def close(): Unit = {
		cluster.close()
	}


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
