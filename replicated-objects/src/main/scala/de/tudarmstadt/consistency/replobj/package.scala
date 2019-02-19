package de.tudarmstadt.consistency

import scala.language.implicitConversions
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
package object replobj {

	def typeToClassTag[T: TypeTag]: ClassTag[T] = {
		ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )
	}


	implicit def refToRefOps[T, L](ref : Ref[T, L]) : RefOps[T, L] = RefOps(ref)

	case class RefOps[T, L](ref : Ref[T, L]) {

		def remote : T = throw new IllegalAccessException("remote can not be accessed here")

		/* syntactic sugar*/
		def apply[R](fieldName : String) : R =
			ref.getField(fieldName)

		def update[R](fieldName : String, value : R) : Unit =
			ref.setField(fieldName, value)

		def <=[R](methodName : String, args : Any*) : R =
			ref.call[R](methodName, args : _*)


	}
}
