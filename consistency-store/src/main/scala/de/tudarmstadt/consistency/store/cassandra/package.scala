package de.tudarmstadt.consistency.store

import java.nio.ByteBuffer
import java.util.UUID

import com.datastax.driver.core._
import de.tudarmstadt.consistency.store.shim.Event.Tx
import de.tudarmstadt.consistency.store.shim.EventRef.TxRef

import scala.reflect.runtime.universe._


/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
package object cassandra {

	type CassandraSession = com.datastax.driver.core.Session


	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")


	private[cassandra] def typeCodecOf[T : TypeTag] : TypeCodec[T] = implicitly[TypeTag[T]] match {
		case TypeTag.Boolean => TypeCodec.cboolean().asInstanceOf[TypeCodec[T]]

		case TypeTag.Int => TypeCodec.cint().asInstanceOf[TypeCodec[T]]
		case t if t == typeTag[Integer] => TypeCodec.cint().asInstanceOf[TypeCodec[T]]
		case t if t == typeTag[java.math.BigInteger] => TypeCodec.varint().asInstanceOf[TypeCodec[T]]

		case TypeTag.Float => TypeCodec.cfloat().asInstanceOf[TypeCodec[T]]
		case TypeTag.Double => TypeCodec.cdouble().asInstanceOf[TypeCodec[T]]
		case t if t == typeTag[java.math.BigDecimal] => TypeCodec.decimal().asInstanceOf[TypeCodec[T]]

		case t if t == typeTag[String] => TypeCodec.varchar().asInstanceOf[TypeCodec[T]]

		case t if t == typeTag[UUID] => TypeCodec.uuid().asInstanceOf[TypeCodec[T]] //TODO Is there a nice way to differentiate between, e.g., UUID and TimeUUID

		case t if t == typeTag[ByteBuffer] => TypeCodec.blob().asInstanceOf[TypeCodec[T]]

		case t => throw new IllegalArgumentException(s"can not infer a type codec from type tag $t with type ${t.tpe}")
	}

	private[cassandra] def runtimeClassOf[T : TypeTag] : Class[T] = {
		val tag = implicitly[TypeTag[T]]
		tag.mirror.runtimeClass(tag.tpe.typeSymbol.asClass).asInstanceOf[Class[T]]
	}



	case class CassandraWriteParams[Consistency](consistency : Consistency)
	case class CassandraReadParams[Id, Consistency](filterForId : Option[Id] = None, consistency : Consistency)
	case class CassandraTxParams[Id, Key, Data, Isolation](tx : Option[Tx[Id, Key, Data]], isolation : Isolation)


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
