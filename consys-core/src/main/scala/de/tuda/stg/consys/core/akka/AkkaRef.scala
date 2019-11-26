package de.tuda.stg.consys.core.akka


import de.tuda.stg.consys.core.{ConsistencyLevel, Ref, ReplicatedObject}


import scala.concurrent.TimeoutException

/**
	* Created on 17.04.19.
	*
	* @author Mirko Köhler
	*/
private[akka] class AkkaRef[Loc, T <: AnyRef](
	val addr : Loc,
	val consistencyLevel : ConsistencyLevel,
	@transient private[akka] var replicaSystem : AkkaReplicaSystem { type Addr = Loc }
) extends Ref[Loc, T] {

	/* Only use this for emergencies */
	def setReplicaSystem(replicaSystem  : AkkaReplicaSystem { type Addr = Loc } ) : Unit = {
		this.replicaSystem = replicaSystem
	}

	override implicit def deref : ReplicatedObject[Loc, T] = replicaSystem match {
		case null => sys.error(s"replica system has not been initialized properly. $toString")

		case _ =>
			val timeout = replicaSystem.defaultTimeout.toNanos
			val startTime = System.nanoTime()

			while (true) {
				replicaSystem.replica.get(addr) match {
					case None => //retry
						if (System.nanoTime() > startTime + timeout)
							throw new TimeoutException(s"the replicated object '$addr' with consistency level $consistencyLevel could not be found on this host.")

						Thread.sleep(200)

					case Some(rob : AkkaReplicatedObject[Loc, T]) =>
						//Check that consistency level of reference matches the referenced object
						assert(rob.consistencyLevel == consistencyLevel, s"non-matching consistency levels. ref was $consistencyLevel and object was ${rob.consistencyLevel}")
						return rob

					case x =>
						throw new IllegalArgumentException(s"AkkaRef expects an AkkaReplicatedObject, but got $x")
				}
			}

			throw new UnknownError("unreachable code. :D")
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