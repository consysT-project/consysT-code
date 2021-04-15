package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.{ConsistencyLabel, Ref}
import scala.concurrent.TimeoutException

/**
	* Created on 17.04.19.
	*
	* @author Mirko Köhler
	*/
private[akka] class AkkaRef[Loc, T](
	val addr : Loc,
	val label : ConsistencyLabel
) extends Ref[Loc, T] {

	type ConsistencyLevel = ConsistencyLabel

	private def getReplicaSystem : AkkaReplicaSystem { type Addr = Loc } =
		AkkaReplicaSystems.system.asInstanceOf[AkkaReplicaSystem { type Addr = Loc }]


	override implicit def deref : AkkaReplicatedObject[Loc, T] = getReplicaSystem match {
		case null => sys.error(s"replica system has not been initialized properly. $toString")

		case replicaSystem =>
			val timeout = replicaSystem.defaultTimeout.toNanos
			val startTime = System.nanoTime()

			while (true) {
				replicaSystem.replica.get(addr) match {
					case None => //retry
						if (System.nanoTime() > startTime + timeout)
							throw new TimeoutException(s"the replicated object '$addr' with consistency level $label could not be found on this host.")

						Thread.sleep(200)

					case Some(rob : AkkaReplicatedObject[Loc, T]) =>
						//Check that consistency level of reference matches the referenced object
						assert(rob.consistencyLevel == label, s"non-matching consistency levels. ref was $label and object was ${rob.consistencyLevel}")
						return rob

					case x =>
						throw new IllegalArgumentException(s"AkkaRef expects an AkkaReplicatedObject, but got $x")
				}
			}

			throw new UnknownError("unreachable code. :D")
	}


	override def isAvailable : Boolean =
		getReplicaSystem.replica.contains(addr)

	override def await() : Unit = {
		getReplicaSystem.replica.waitFor(addr)
	}

	override def delete() : Unit = {
		getReplicaSystem.delete(addr)
	}


	override def toString : String = s"RefImpl($addr, $label)"
}