package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.storelayer.distribution.SessionService

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraSessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] extends SessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {
	type CassandraSession = com.datastax.driver.core.Session

	val session : CassandraSession
	val cluster : Cluster
	val keyspaceName : String
	val typeBinding : CassandraTypeBinding[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]


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
