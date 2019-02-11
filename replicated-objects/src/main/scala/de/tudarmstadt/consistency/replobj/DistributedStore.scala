package de.tudarmstadt.consistency.replobj

import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait DistributedStore[Addr] {

	def distribute[T, L : TypeTag](addr : Addr, value : T) : Ref[T, L]

	def replicate[T, L : TypeTag](addr : Addr) : Ref[T, L]

	def ref[T, L](addr : Addr) : Ref[T, L]


	abstract class Ref[T, L : TypeTag] {

		def getField[R](fieldName : String) : R

		def setField[R](fieldName : String, value : R) : Unit

		def call[R](methodName : String, args : Any*) : R


		/* syntactic sugar*/
		def apply[R](fieldName : String) : R =
			getField(fieldName)

		def update[R](fieldName : String, value : R) : Unit =
			setField(fieldName, value)

		def <=[R](methodName : String, args : Any*) : R =
			call[R](methodName, args : _*)
	}
}
