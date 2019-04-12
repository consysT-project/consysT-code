package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ReplicatedObject

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait LockableReplicatedObject[T <: AnyRef] extends ReplicatedObject[T] {

	private[actors] def lock(txid : Long) : Unit

	private[actors] def unlock(txid : Long) : Unit

}
