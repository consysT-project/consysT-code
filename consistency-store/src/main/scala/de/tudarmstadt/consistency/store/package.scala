package de.tudarmstadt.consistency

import java.util.UUID

import com.datastax.driver.core.Cluster

import scala.reflect.runtime.universe._

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
package object store {


	trait IdOps[T] {
		def freshId() : T
	}

	trait KeyOps[T] {
		def transactionKey : T
	}

	trait TxStatusOps[T] {
		def pending : T
		def committed : T
		def aborted : T
	}

	trait IsolationLevelOps[T] {
		def snapshotIsolation : T
		def readUncommitted : T
		def readCommitted : T
		def none : T
	}

	trait ConsistencyLevelOps[T] {
		def sequential : T
	}


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
		case class Success[Id, Key, Data](key : Key, id : Id, data : Data, deps : Set[Id]) extends ReadStatus[Id, Key, Data]
		case class NotFound[Id, Key, Data](key : Key, description : String) extends ReadStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends ReadStatus[Id, Key, Data]
	}

	trait WriteStatus[Id, Key, Data]
	object WriteStatus {
		case class Success[Id, Key, Data](id : Id, key : Key, data : Data) extends WriteStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends WriteStatus[Id, Key, Data]
	}


	case class CassandraWriteParams[Id, Consistency](id : Id, deps : Set[Id], consistency : Consistency)
	case class CassandraReadParams[Consistency](consistency : Consistency)
	case class CassandraTxParams[Id, Isolation](txid : Id, isolation : Isolation)



	trait ConnectionParams {
		def connectCluster : Cluster
	}

	object ConnectionParams {
		class AddressAndPort(address : String, port : Int) extends ConnectionParams {
			override def connectCluster : Cluster =
				Cluster.builder.addContactPoint(address).withPort(port).build
		}

		object LocalCluster extends AddressAndPort("127.0.0.1", 9042)
	}






	private[store] def runtimeClassOf[T : TypeTag] : Class[T] = {
		val tag = implicitly[TypeTag[T]]
		tag.mirror.runtimeClass(tag.tpe.typeSymbol.asClass).asInstanceOf[Class[T]]
	}

	private[store] def cassandraTypeOf[T : TypeTag] : String = implicitly[TypeTag[T]] match {

		//TODO: Is it possible to use CodecRegistry and/or DataType for that task?

		case t if t == typeTag[Boolean] => "boolean"

		case t if t == typeTag[Int] || t == typeTag[Integer] => "int"

		case t if t == typeTag[Float] => "float"
		case t if t == typeTag[Double] => "double"
		case t if t == typeTag[BigDecimal] => "decimal"

		case t if t == typeTag[String] => "text"

		case t if t == typeTag[UUID] => "uuid" //TODO Differentiate between UUID and TimeUUID

		case t => throw new IllegalArgumentException(s"can not infer a cassandra type from type tag $t")
	}

}
