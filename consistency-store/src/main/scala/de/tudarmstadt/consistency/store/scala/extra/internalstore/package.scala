package de.tudarmstadt.consistency.store.scala.extra

import java.util.UUID

import com.datastax.driver.core.{Cluster, Row}

import scala.reflect.runtime.universe._


/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
package object internalstore {

	/**
		* Type of sessions of the Cassandra database.
		*/


	trait ConnectionParams {
		def connectCluster : Cluster
	}

	class ConnectAddressPort(address : String, port : Int) extends ConnectionParams {
		override def connectCluster : Cluster =
			Cluster.builder.addContactPoint(address).withPort(port).build
	}

	object LocalClusterParams extends ConnectAddressPort("127.0.0.1", 9042)


	case class CassandraUpdate[Id, Key, Data](id : Id, key : Key, data : Data, dependencies : Set[Id])



	private[internalstore] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")







}
