package de.tuda.stg.consys.core.store

/**
 * Created on 14.01.20.
 *
 * @author Mirko Köhler
 */
trait StoredObject[StoreType <: Store, T <: StoreType#ObjType] {

	def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R

	def getField[R](fieldName : String) : R

	def setField[R](fieldName : String, value : R) : Unit

	/* for Java binding */
	final def invoke[R](methodName : String, args : Array[Any]) : R =
		invoke[R](methodName, Seq(args.toSeq))
}
