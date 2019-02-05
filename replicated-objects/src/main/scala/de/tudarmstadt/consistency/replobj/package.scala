package de.tudarmstadt.consistency

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
}
