package de.tuda.stg.consys.objects.actors

import de.tuda.stg.consys.objects.ReplicatedObject
import de.tuda.stg.consys.objects.ReplicatedObject

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait LockableReplicatedObject[T <: AnyRef] extends ReplicatedObject[T] {

	private[actors] def lock(txid : Long) : Unit

	private[actors] def unlock(txid : Long) : Unit

}
