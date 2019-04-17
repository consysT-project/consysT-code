package de.tudarmstadt.consistency.replobj


/**
	* Created on 28.02.19.
	*
	* @author Mirko Köhler
	*/
trait Ref[Addr, T <: AnyRef] extends Serializable {

	val addr : Addr
	val consistencyLevel : ConsistencyLevel

	def deref : ReplicatedObject[T]

	/* shortcut for Java implementation */
	final def remote : T = deref.remote
}