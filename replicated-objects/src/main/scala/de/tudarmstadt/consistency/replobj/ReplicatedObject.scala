package de.tudarmstadt.consistency.replobj

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/

trait ReplicatedObject[T <: AnyRef, L] {

	def getField[R](fieldName : String) : R

	def setField[R](fieldName : String, value : R) : Unit

	def invoke[R](methodName : String, args : Any*) : R

	def synchronize() : Unit

	//Optional print method for debugging purposes
	private[replobj] def print() : Unit = throw new UnsupportedOperationException("print is not supported")



	/*this syntax can only be used with the preprocessor. The preprocessor rewrites calls to .remote.*/
	final def remote : T = throw new IllegalAccessException("remote can not be accessed here")

	/*syntactic sugar*/
	final def apply[R](fieldName : String) : R =
		getField(fieldName)

	final def update[R](fieldName : String, value : R) : Unit =
		setField(fieldName, value)

	final def <=[R](methodName : String, args : Any*) : R =
		invoke[R](methodName, args : _*)
}
