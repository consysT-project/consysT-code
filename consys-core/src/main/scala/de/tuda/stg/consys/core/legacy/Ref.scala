package de.tuda.stg.consys.core.legacy

/**
	* Created on 28.02.19.
	*
	* @author Mirko Köhler
	*/
trait Ref[Addr, T] extends Serializable {
	/** Type of consistency labels */
	type ConsistencyLevel

	val addr : Addr

	val label : ConsistencyLevel

	def deref : ReplicatedObject[Addr, T] {type ConsistencyLevel = Ref.this.ConsistencyLevel}

	def isAvailable : Boolean

	def await() : Unit

	def delete() : Unit


	/* shortcut for Java implementation */
	final def ref : T = deref.ref
}
