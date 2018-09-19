package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.{Cluster, ConsistencyLevel}
import com.datastax.driver.core.querybuilder.QueryBuilder

/**
	* Created on 19.09.18.
	*
	* @author Mirko Köhler
	*/
private [cassandra] object Keyspaces {
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

		def reset(cluster : Cluster) : Unit = {
			var session = cluster.connect(name)

			txTable.truncate(session)
			keyTable.truncate(session)
			dataTable.truncate(session)

			session.close()
		}
	}



	trait TableDef {
		val name : String
		def create(session : CassandraSession)

		def truncate(session : CassandraSession): Unit = {
			session.execute(QueryBuilder.truncate(name).setConsistencyLevel(ConsistencyLevel.ALL))
		}
	}



	/**
		* Defines the keyspace that is used for the store.
		*/
	def createCassandraKeyspaceFor(store : SysnameCassandraStore[_, _, _, _, _, _]) : KeyspaceDef = new KeyspaceDef {
		import store._

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

		}


		override val txTable : TableDef = new TableDef {
			override val name : String = "t_tx"
			override def create(session : CassandraSession) : Unit = {
				session.execute(
					s"""CREATE TABLE $name
						 | (txid ${idType.getCqlType.asFunctionParameterString},
						 | status ${txStatusType.getCqlType.asFunctionParameterString},
						 | isolation ${isolationType.getCqlType.asFunctionParameterString},
						 | PRIMARY KEY(txid))""".stripMargin
				)
			}
		}


		override val keyTable : TableDef = new TableDef {
			override val name : String = "t_keys"
			override def create(session : CassandraSession) : Unit = {
				session.execute(
					s"""CREATE TABLE $name
						 | (key ${keyType.getCqlType.asFunctionParameterString},
						 | txid ${idType.getCqlType.asFunctionParameterString},
						 | reads set<${idType.getCqlType.asFunctionParameterString}>,
						 | PRIMARY KEY(key))""".stripMargin
				)
			}
		}

		override val dataTable : TableDef = new TableDef {
			override val name : String = "t_data"
			override def create(session : CassandraSession) : Unit = {
				session.execute(
					s"""CREATE TABLE $name
						 | (id ${idType.getCqlType.asFunctionParameterString()},
						 | key ${keyType.getCqlType.asFunctionParameterString},
						 | data ${dataType.getCqlType.asFunctionParameterString},
						 | deps set<frozen<tuple<${idType.getCqlType.asFunctionParameterString}, ${keyType.getCqlType.asFunctionParameterString}>>>,
						 | txid ${idType.getCqlType.asFunctionParameterString},
						 | txstatus ${txStatusType.getCqlType.asFunctionParameterString},
						 | consistency ${consistencyType.getCqlType.asFunctionParameterString},
						 | isolation ${isolationType.getCqlType.asFunctionParameterString},
						 | PRIMARY KEY (key, id))""".stripMargin
				)
			}
		}
	}
}



