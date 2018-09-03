package de.tudarmstadt.consistency.store.scala

import java.util.UUID

import scala.reflect.runtime.universe._

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
package object extra {

	private[extra] def runtimeClassOf[T : TypeTag] : Class[T] = {
		val tag = implicitly[TypeTag[T]]
		tag.mirror.runtimeClass(tag.tpe.typeSymbol.asClass).asInstanceOf[Class[T]]
	}

	private[extra] def cassandraTypeOf[T : TypeTag] : String = implicitly[TypeTag[T]] match {

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
