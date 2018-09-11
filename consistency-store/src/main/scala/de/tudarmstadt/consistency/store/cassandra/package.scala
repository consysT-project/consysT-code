package de.tudarmstadt.consistency.store

import java.math.BigInteger
import java.nio.ByteBuffer
import java.util.UUID

import com.datastax.driver.core._
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

}
