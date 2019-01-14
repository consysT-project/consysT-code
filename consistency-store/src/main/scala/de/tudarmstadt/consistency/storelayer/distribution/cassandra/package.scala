package de.tudarmstadt.consistency.storelayer.distribution

import com.datastax.driver.core.{Cluster, Row, TupleValue}

/**
	* Created on 08.01.19.
	*
	* @author Mirko Köhler
	*/
package object cassandra {

	private[cassandra] def tupleToCassandraTuple[A,B](tuple : (A,B))(implicit sessionBinding : CassandraSessionService[_, _, _, _, _, _, _]) : TupleValue = {
		import sessionBinding._
		import sessionBinding.typeBinding._

		val typ = cluster.getMetadata.newTupleType(TypeCodecs.Id.getCqlType, TypeCodecs.Key.getCqlType)
		typ.newValue(tuple._1.asInstanceOf[AnyRef], tuple._2.asInstanceOf[AnyRef])
	}

	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")



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
		private[storelayer] object LocalClusterNode1 extends AddressAndPort("127.0.0.1", 9042)
		private[storelayer] object LocalClusterNode2 extends AddressAndPort("127.0.0.2", 9042)
		private[storelayer] object LocalClusterNode3 extends AddressAndPort("127.0.0.3", 9042)
	}

}
