package de.tuda.stg.consys.core.store

/**
 * Trait for objects that are stored in a store.
 */
trait Handler[StoreType <: Store, T <: StoreType#ObjType] {

	/** Invokes a method on the stored object. */
	def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R

	/** Reads a field of the stored object. */
	def getField[R](fieldName : String) : R

	/** Writes a field of the stored object */
	def setField[R](fieldName : String, value : R) : Unit

	/* for Java binding */
	final def invoke[R](methodName : String, args : Array[Any]) : R =
		invoke[R](methodName, Seq(args.toSeq))
}
