package de.tudarmstadt.consistency.store

import com.datastax.driver.core.{Cluster, Row}
import scala.collection.JavaConverters
import scala.reflect.runtime.universe._


/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
package object cassandra {

	/**
		* Type of sessions of the Cassandra database.
		*/





	case class CassandraUpdate[Id, Key, Data](id : Id, key : Key, data : Data, dependencies : Set[Id])



	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")



	trait DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		def id : Id
		def key : Key
		def data : Data
		def deps : Set[Id]
		def txid : Option[Id]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency
	}

	case class CassandraRow[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](row : Row) extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		override def id : Id = row.get("id", runtimeClassOf[Id])
		override def key : Key = row.get("key", runtimeClassOf[Key])
		override def data : Data = row.get("data", runtimeClassOf[Data])
		override def deps : Set[Id] = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[Id])).toSet
		override def txid : Option[Id] = Option(row.get("txid", runtimeClassOf[Id]))
		override def txStatus : TxStatus = row.get("txstatus", runtimeClassOf[TxStatus])
		override def isolation : Isolation = row.get("isolation", runtimeClassOf[Isolation])
		override def consistency : Consistency = row.get("consistency", runtimeClassOf[Consistency])
	}

	case class LocalRow[Id, Key, Data, TxStatus, Isolation, Consistency](id : Id, key : Key, data : Data, deps : Set[Id], txid : Option[Id], txStatus : TxStatus, isolation : Isolation, consistency : Consistency)
		extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]






}
