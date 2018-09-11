package de.tudarmstadt.consistency

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.store.shim.EventRef
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

import scala.reflect.runtime.universe._

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


	trait CommitStatus[Id, Key]
	object CommitStatus {
		//The transaction successfully committed
		case class Success[Id, Key](txid : Id, writtenIds : Iterable[EventRef[Id, Key]]) extends CommitStatus[Id, Key]

		//The transaction has been aborted and changes have been rolled back.
		case class Abort[Id, Key](txid : Id, description : String) extends CommitStatus[Id, Key]

		//The transaction indicated an error. It is unclear whether it (partially) committed or aborted completely.
		case class Error[Id, Key](txid : Id, error : Throwable) extends CommitStatus[Id, Key]
	}

	trait ReadStatus[Id, Key, Data]
	object ReadStatus {
		case class Success[Id, Key, Data](key : Key, id : Id, data : Data, deps : Set[UpdateRef[Id, Key]]) extends ReadStatus[Id, Key, Data]
		case class NotFound[Id, Key, Data](key : Key, description : String) extends ReadStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends ReadStatus[Id, Key, Data]
	}

	trait WriteStatus[Id, Key, Data]
	object WriteStatus {
		case class Success[Id, Key, Data](id : Id, key : Key, data : Data) extends WriteStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends WriteStatus[Id, Key, Data]
	}


	case class CassandraWriteParams[Consistency](consistency : Consistency)
	case class CassandraReadParams[Id, Consistency](filterForId : Option[Id] = None, consistency : Consistency)
	case class CassandraTxParams[Id, Isolation](txid : Option[TxRef[Id]], isolation : Isolation)



	trait ConnectionParams {
		def connectCluster : Cluster
	}

	object ConnectionParams {
		class AddressAndPort(address : String, port : Int) extends ConnectionParams {
			override def connectCluster : Cluster =
				Cluster.builder.addContactPoint(address).withPort(port).build
		}

		//Special params for connecting to Cassandra started locally with ccm
		object LocalCluster extends AddressAndPort("127.0.0.1", 9042)
		object LocalClusterNode1 extends AddressAndPort("127.0.0.1", 9042)
		object LocalClusterNode2 extends AddressAndPort("127.0.0.2", 9042)
		object LocalClusterNode3 extends AddressAndPort("127.0.0.3", 9042)
	}







}
