package de.tudarmstadt.consistency.store

import java.util.UUID

import com.datastax.driver.core.{Cluster, DataType, Row, TupleValue}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

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


//	case class CassandraUpdate[Id, Key, Data](id : Id, key : Key, data : Data, dependencies : Set[EventRef[Id, Key]]) {
//		def toEventRef : EventRef[Id, Key] =
//			EventRef(id, key)
//	}


	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")

	trait DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		def id : Id
		def key : Key
		def data : Data
		def deps : Set[UpdateRef[Id, Key]]
		def txid : Option[TxRef[Id]]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency
	}

	case class CassandraRow[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](row : Row) extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		override def id : Id = row.get("id", runtimeClassOf[Id])
		override def key : Key = row.get("key", runtimeClassOf[Key])
		override def data : Data = row.get("data", runtimeClassOf[Data])
		override def deps : Set[UpdateRef[Id, Key]] = {
			val rawSet : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[TupleValue])).toSet
			rawSet.map(tv => {
				val id = tv.get(0, runtimeClassOf[Id])
				val key = tv.get(1, runtimeClassOf[Key])
				UpdateRef(id, key)
			})
		}
		override def txid : Option[TxRef[Id]] = Option(TxRef(row.get("txid", runtimeClassOf[Id])))
		override def txStatus : TxStatus = row.get("txstatus", runtimeClassOf[TxStatus])
		override def isolation : Isolation = row.get("isolation", runtimeClassOf[Isolation])
		override def consistency : Consistency = row.get("consistency", runtimeClassOf[Consistency])
	}

	case class LocalRow[Id, Key, Data, TxStatus, Isolation, Consistency](id : Id, key : Key, data : Data, deps : Set[UpdateRef[Id, Key]], txid : Option[TxRef[Id]], txStatus : TxStatus, isolation : Isolation, consistency : Consistency)
		extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]



	private[store] def cassandraTypeOf[T : TypeTag] : DataType = implicitly[TypeTag[T]] match {

		//TODO: Is it possible to use CodecRegistry and/or DataType for that task?

		case t if t == typeTag[Boolean] => DataType.cboolean()

		case t if t == typeTag[Int] || t == typeTag[Integer] => DataType.cint()

		case t if t == typeTag[Float] => DataType.cfloat()
		case t if t == typeTag[Double] => DataType.cdouble()
		case t if t == typeTag[BigDecimal] => DataType.decimal()

		case t if t == typeTag[String] => DataType.text()

		case t if t == typeTag[UUID] => DataType.uuid() //TODO Differentiate between UUID and TimeUUID

		case t => throw new IllegalArgumentException(s"can not infer a cassandra type from type tag $t")
	}




}
