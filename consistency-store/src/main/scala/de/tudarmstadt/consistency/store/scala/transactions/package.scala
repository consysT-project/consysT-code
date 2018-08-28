package de.tudarmstadt.consistency.store.scala

import java.util.UUID

import com.datastax.driver.core.{Cluster, Row}

import scala.reflect.runtime.universe._


/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
package object transactions {

	/**
		* Type of sessions of the Cassandra database.
		*/
	type CassandraSession = com.datastax.driver.core.Session


	trait ConnectionParams {
		def connectCluster : Cluster
	}

	class ConnectAddressPort(address : String, port : Int) extends ConnectionParams {
		override def connectCluster : Cluster =
			Cluster.builder.addContactPoint(address).withPort(port).build
	}

	object LocalClusterParams extends ConnectAddressPort("127.0.0.1", 9042)



	trait CommitStatus[Id, Return]
	object CommitStatus {
		//The transaction successfully committed
		case class Success[Id, Return](txid : Id, writtenIds : Set[Id], result : Return) extends CommitStatus[Id, Return]

		//The transaction has been aborted and changes have been rolled back.
		case class Abort[Id, Return](txid : Id, description : String) extends CommitStatus[Id, Return]

		//The transaction indicated an error. It is unclear whether it (partially) committed or aborted comnpletely.
		case class Error[Id, Return](txid : Id, error : Throwable) extends CommitStatus[Id, Return]

	}

	trait ReadStatus[Id, Key, Data]
	object ReadStatus {
		case class Success[Id, Key, Data](key : Key, id : Id, data : Data) extends ReadStatus[Id, Key, Data]
		case class NotFound[Id, Key, Data](key : Key, description : String) extends ReadStatus[Id, Key, Data]
		case class Abort[Id, Key, Data](key : Key, description : String) extends ReadStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends ReadStatus[Id, Key, Data]
	}




	private[transactions] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")


	private[transactions] def runtimeClassOf[T : TypeTag] : Class[T] = {
		val tag = implicitly[TypeTag[T]]
		tag.mirror.runtimeClass(tag.tpe.typeSymbol.asClass).asInstanceOf[Class[T]]
	}

	private[transactions] def cassandraTypeOf[T : TypeTag] : String = implicitly[TypeTag[T]] match {

		//TODO: Is it possible to use CodecRegistry and/or DataType for that task?

		case t if t == typeTag[Boolean] => "boolean"

		case t if t == typeTag[Int] => "int"

		case t if t == typeTag[Float] => "float"
		case t if t == typeTag[Double] => "double"
		case t if t == typeTag[BigDecimal] => "decimal"

		case t if t == typeTag[String] => "text"

		case t if t == typeTag[UUID] => "uuid" //TODO Differentiate between UUID and TimeUUID

		case t => throw new IllegalArgumentException(s"can not infer a cassandra type from type tag $t")
	}




}
