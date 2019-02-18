package de.tudarmstadt.consistency.replobj

import scala.reflect.runtime.universe._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/

abstract class Ref[T, L : TypeTag] extends Serializable {

	def remote : T = throw new IllegalAccessException("remote can not be accessed here")

	private[replobj] def getField[R](fieldName : String) : R

	private[replobj] def setField[R](fieldName : String, value : R) : Unit

	private[replobj] def call[R](methodName : String, args : Any*) : R

	//Optional print method for debugging purposes
	private[replobj] def print() : Unit = throw new UnsupportedOperationException("print is not supported")


	/* syntactic sugar*/
	def apply[R](fieldName : String) : R =
		getField(fieldName)

	def update[R](fieldName : String, value : R) : Unit =
		setField(fieldName, value)

	def <=[R](methodName : String, args : Any*) : R =
		call[R](methodName, args : _*)
}
