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



	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")





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
