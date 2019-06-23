package de.tuda.stg.consys.objects.crdt

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.crdt.CRDT.{Operation, ReplicaId}
import de.tuda.stg.consys.objects.crdt.OpBasedCRDT.{RegisterAtReplica, RegisterReplica}
import de.tuda.stg.consys.objects.crdt.StateBasedCRDT.StateChanged

import scala.collection.mutable

/**
	* Created on 14.06.19.
	*
	* @author Mirko Köhler
	*/
trait RepCRDT[T] extends CRDT[T] {

	protected val otherReplicas : mutable.Map[ReplicaId, ActorRef] = new mutable.HashMap()

	protected def doRegisterReplica(id : ReplicaId, ref : ActorRef) : Unit = { }

	override def receive : Receive = {
		case RegisterReplica(id, ref) =>
			otherReplicas(id) = ref
			doRegisterReplica(id, ref)

		case RegisterAtReplica(ref) =>
			ref ! RegisterReplica(replicaId, self)

		//case _ => super.receive
	}


}
