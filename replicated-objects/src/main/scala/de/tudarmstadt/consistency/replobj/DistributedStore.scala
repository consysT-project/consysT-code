package de.tudarmstadt.consistency.replobj

import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait DistributedStore[Addr, Path] {

	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using a path generated from the specified address.
		* @param addr The (distributed) address of the object
		* @param value The object to distribute
		* @return A reference to the created object
		*/
	def distribute[T : TypeTag, L : TypeTag](addr : Addr, value : T) : Ref[T, L]


	def replicate[T : TypeTag, L : TypeTag](path : Path) : Ref[T, L]

	def ref[T, L](path : Path) : Ref[T, L]


	abstract class Ref[T, L : TypeTag] {

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
}
