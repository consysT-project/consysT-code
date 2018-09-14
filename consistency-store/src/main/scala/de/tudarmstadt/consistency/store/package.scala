package de.tudarmstadt.consistency

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.store.shim.EventRef
import de.tudarmstadt.consistency.store.shim.EventRef.TxRef

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
package object store {


	trait Ids[T] {
		def freshId() : T
	}

	trait Keys[T] {
		def transactionKey : T
	}

	trait TxStatuses[T] {
		def pending : T
		def committed : T
		def aborted : T
	}

	trait IsolationLevels[T] {
		def snapshotIsolation : T
		def readUncommitted : T
		def readCommitted : T
		def none : T
	}

	trait ConsistencyLevels[T] {
		def causal : T
		def weak : T
	}


	case class CassandraWriteParams[Consistency](consistency : Consistency)
	case class CassandraReadParams[Id, Consistency](filterForId : Option[Id] = None, consistency : Consistency)
	case class CassandraTxParams[Id, Isolation](txid : Option[TxRef[Id]], isolation : Isolation)


	trait ConnectionParams {
		def connectCluster : Cluster
	}

	object ConnectionParams {
		class AddressAndPort(address : String, port : Int)
			extends UsingClusterBuilder(builder => builder.addContactPoint(address).withPort(port))

		class UsingClusterBuilder(make : Cluster.Builder => Cluster.Builder) extends ConnectionParams {
			override def connectCluster : Cluster =
				make(Cluster.builder).build()
		}

		//Special params for connecting to Cassandra started locally with ccm
		object LocalCluster extends AddressAndPort("127.0.0.1", 9042)

		//Special local cluster nodes that can be used for testing
		private[store] object LocalClusterNode1 extends AddressAndPort("127.0.0.1", 9042)
		private[store] object LocalClusterNode2 extends AddressAndPort("127.0.0.2", 9042)
		private[store] object LocalClusterNode3 extends AddressAndPort("127.0.0.3", 9042)
	}







}
