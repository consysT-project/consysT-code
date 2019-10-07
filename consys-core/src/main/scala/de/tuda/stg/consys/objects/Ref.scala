package de.tuda.stg.consys.objects

/**
	* Created on 28.02.19.
	*
	* @author Mirko Köhler
	*/
trait Ref[Addr, T <: AnyRef] extends Serializable {

	val addr : Addr
	val consistencyLevel : ConsistencyLevel

	def deref : ReplicatedObject[Addr, T]

	def isAvailable : Boolean

	def await() : Unit

	def delete() : Unit


	/* shortcut for Java implementation */
	final def ref : T = deref.ref
}