package de.tudarmstadt.consistency.store.scala.transactions

import java.util.UUID

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.querybuilder.QueryBuilder.select
import com.datastax.driver.core.{Cluster, Row, Session}
import de.tudarmstadt.consistency.store.scala.transactions.ReadStatus.NotFound
import de.tudarmstadt.consistency.store.scala.transactions.exceptions.UnsupportedIsolationLevelException
import de.tudarmstadt.consistency.utils.Log

import scala.reflect.runtime.universe._

/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameBaseStore[Id, Key, Data, TxStatus, Consistency, Isolation] extends SysnameStore[Id, Key, Data, TxStatus, Consistency, Isolation] {


	protected val connectionParams : ConnectionParams

	protected var cluster : Cluster =
		connectionParams.connectCluster


	override def commit[Return](session : CassandraSession, transaction : Transaction[Return], isolation : Isolation)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return] =
		throw new UnsupportedIsolationLevelException(isolation)



	override def read(session : CassandraSession, key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : ReadStatus[Id, Key, Data] = {
		//Retrieve the maximum id for a given key
		val maxResult = session.execute(select().max("id")
			.from(keyspace.dataTable.name)
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
			.from(keyspace.dataTable.name)
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

		val isolation = readRow.get("isolation", runtimeClassOf[Isolation])

		internalRead(session, readId, key, isolation, readRow)
	}

	protected def internalRead(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]): ReadStatus[Id, Key, Data] =
		throw new UnsupportedIsolationLevelException(isolation)


	def initializeKeyspace()(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]): Unit = {
		keyspace.initialize(cluster)
	}

	override def newSession : CassandraSession =
		cluster.connect(keyspace.name)

	/**
		* Defines the keyspace that is used for the store.
		*/
	val keyspace : KeyspaceDef = new KeyspaceDef {
		override val name : String = "k_sysname"

		override protected def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = {
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
			override def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (txid ${cassandraTypeOf[Id]},
					 | status ${cassandraTypeOf[TxStatus]},
					 | isolation ${cassandraTypeOf[Isolation]},
					 | PRIMARY KEY(txid));""".stripMargin
			)
		}

		override val keyTable : TableDef = new TableDef {
			override val name : String = "t_keys"
			override def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = session.execute(
				s"""CREATE TABLE $name
					 | (key ${cassandraTypeOf[Key]},
					 | txid ${cassandraTypeOf[Id]},
					 | PRIMARY KEY(key));""".stripMargin
			)
		}

		override val dataTable : TableDef = new TableDef {
			override val name : String = "t_data"
			override def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = session.execute(
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
	protected val maxFunctionDef : String


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
		protected def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit

		def initialize(cluster : Cluster)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = {
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
		def create(session : CassandraSession)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation])
	}

	/* temporary for debugging */
	def printTables(session : Session): Unit = {
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
