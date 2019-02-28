package de.tudarmstadt.consistency.replobj


/**
	* Created on 28.02.19.
	*
	* @author Mirko Köhler
	*/
trait Ref[Addr, T, L] extends Serializable {

	val addr : Addr

	def toReplicatedObject : ReplicatedObject[T, L]
}