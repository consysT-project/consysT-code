package de.tuda.stg.consys.objects.actors

import java.util.concurrent.locks.LockSupport

import de.tuda.stg.consys.objects.{ConsistencyLevel, Ref, Replicated, ReplicatedObject}

/**
	* Created on 17.04.19.
	*
	* @author Mirko Köhler
	*/
private[actors] class AkkaRef[Addr, T <: AnyRef](val addr : Addr, val consistencyLevel : ConsistencyLevel, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T] {

	override implicit def deref : ReplicatedObject[Addr, T] = replicaSystem match {
		case null => sys.error(s"replica system has not been initialized properly. $toString")

		case _ => replicaSystem.replica.get(addr) match {
			case None => //retry
				sys.error(s"the replicated object '$addr' with consistency level $consistencyLevel is not available on this host.")

			case Some(rob : AkkaReplicatedObject[Addr, T]) =>
				//Check that consistency level of reference matches the referenced object
				assert(rob.consistencyLevel == consistencyLevel, s"non-matching consistency levels. ref was $consistencyLevel and object was ${rob.consistencyLevel}")

				rob

			case x => throw new IllegalArgumentException(s"AkkaRef expects an AkkaReplicatedObject, but got $x")
		}
	}


	override def isAvailable : Boolean =
		replicaSystem.replica.contains(addr)

	override def await() : Unit = {
		replicaSystem.replica.waitFor(addr)
	}

	override def delete() : Unit = {
		replicaSystem.delete(addr)
	}


	override def toString : String = s"RefImpl($addr, $consistencyLevel)"
}