package de.tuda.stg.consys.core.legacy

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/

trait ReplicatedObject[Addr, T] {

	type ConsistencyLevel

	def addr : Addr

	def consistencyLevel : ConsistencyLevel

	def getField[R](fieldName : String) : R

	def setField[R](fieldName : String, value : R) : Unit

//	def invokeWithLocks[R](methodName : String, args : Seq[Seq[Any]], usesObjects : Iterable[Addr]) : R

	//args is Seq[Seq[...]], because they can appear in multiple argument lists
	def invoke[R](methodName : String, args : Seq[Seq[Any]]) : R
//		invokeWithLocks(methodName, args, Iterable.empty)

	final def invoke[R](methodName : String) : R =
		//invokes a method with no parameter list. Use Seq(Seq()) for methods with an empty parameter list!
		invoke(methodName, Seq())

	/* for Java binding */
	final def invoke[R](methodName : String, args : Array[Any]) : R =
		invoke[R](methodName, Seq(args.toSeq))

	def sync() : Unit

	def syncAll() : Unit

	//Optional print method for debugging purposes
	def print() : Unit = throw new UnsupportedOperationException("print is not supported")

	/*this syntax can only be used with the preprocessor. The preprocessor rewrites calls to .ref.*/
	final def ref : T =
		throw new UnsupportedOperationException("ref can not be called. use a preprocessor to replace all calls to ref.")

	/*syntactic sugar*/
	final def apply[R](fieldName : String) : R =
		getField(fieldName)

	final def update[R](fieldName : String, value : R) : Unit =
		setField(fieldName, value)

	final def <=[R](methodName : String, args : Any*) : R =
		invoke[R](methodName, Seq(args))
}
