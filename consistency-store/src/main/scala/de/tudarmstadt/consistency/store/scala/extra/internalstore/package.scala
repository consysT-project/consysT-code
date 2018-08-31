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


	private[internalstore] def runtimeClassOf[T : TypeTag] : Class[T] = {
		val tag = implicitly[TypeTag[T]]
		tag.mirror.runtimeClass(tag.tpe.typeSymbol.asClass).asInstanceOf[Class[T]]
	}

	private[internalstore] def cassandraTypeOf[T : TypeTag] : String = implicitly[TypeTag[T]] match {

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
