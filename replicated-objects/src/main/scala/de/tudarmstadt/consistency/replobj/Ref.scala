package de.tudarmstadt.consistency.replobj

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/

trait Ref[T, L] extends Serializable {

	def getField[R](fieldName : String) : R

	def setField[R](fieldName : String, value : R) : Unit

	def call[R](methodName : String, args : Any*) : R

	//Optional print method for debugging purposes
	private[replobj] def print() : Unit = throw new UnsupportedOperationException("print is not supported")
}

object Ref {

	trait LocalRef[T, L] extends Ref[T, L] {
		def merge() : Unit
	}

	trait RemoteRef[T, L] extends Ref[T, L]
}
