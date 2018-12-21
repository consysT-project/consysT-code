package de.tudarmstadt.consistency.storelayer.cassandra

import com.datastax.driver.core.Cluster

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait SessionBinding[Id, Key, Data, TxStatus, Isolation, Consistency] {
	type CassandraSession = com.datastax.driver.core.Session

	val session : CassandraSession
	val cluster : Cluster
	val keyspaceName : String
	val typeBinding : CassandraTypeBinding[Id, Key, Data, TxStatus, Isolation, Consistency]

	/* class definitions */

	/* references to other database entries */
	case class OpRef(id : Id, key : Key) {
		assert(id != null)
		assert(key != null)
		def toTuple : (Id, Key) =	(id, key)
	}
	case class TxRef(id : Id) {
		assert(id != null)
	}


	/* queries */

	def CREATE_KEYSPACE(): Unit = {
		//Strategy NetworkTopologyStrategy does not support a replication factor.
		//Initialize the keyspace
		session.execute(s"DROP KEYSPACE IF EXISTS $keyspaceName;")
		session.execute(
			s"""CREATE KEYSPACE $keyspaceName
				 | WITH replication = {'class': 'SimpleStrategy', 'replication_factor': 3 };""".stripMargin
		)

		USE_KEYSPACE()
	}

	def USE_KEYSPACE(): Unit = {
		//Use the keypsace as default keyspace
		session.execute(s"USE $keyspaceName;")
	}




}
