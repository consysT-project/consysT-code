package de.tuda.stg.consys.objects.crdt

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.crdt.CRDT.{Operation, ReplicaId, SequenceNumber}
import de.tuda.stg.consys.objects.crdt.OpBasedCRDT.{Mutation, OpCache, RegisterAtReplica, RegisterReplica}
import de.tuda.stg.consys.objects.crdt.StateBasedCRDT.StateChanged

import scala.collection.mutable

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
abstract class StateBasedCRDT[T] extends CRDT[T] {

	protected [crdt] def initialState : T
	protected var state : T = initialState

	private val otherReplicas : mutable.Map[ReplicaId, ActorRef] = new mutable.HashMap()

	def merge(otherState : T) : Unit

	override def receive : Receive = {
		case op : Operation =>
			handleOperation(op) match {
				case None =>
					require(!op.isReturning)
				case Some(ret) =>
					require(op.isReturning)
					sender() ! ret
			}

			if (op.isMutating) {
				otherReplicas.values.foreach(rep => rep ! StateChanged(replicaId, state))
			}

		case StateChanged(id, otherState : T) =>
			merge(otherState)

		case RegisterReplica(id, ref) =>
			otherReplicas(id) = ref

		case RegisterAtReplica(ref) =>
			ref ! RegisterReplica(replicaId, self)

	}
}

object StateBasedCRDT {

	case class StateChanged[T](id : ReplicaId, newState : T)
}


