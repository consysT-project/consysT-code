package de.tuda.stg.consys.objects.crdt

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.crdt.CRDT.{Operation, ReplicaId, SequenceNumber}
import de.tuda.stg.consys.objects.crdt.OpBasedCRDT.{Mutation, OpCache, RegisterAtReplica, RegisterReplica}
import de.tuda.stg.consys.objects.crdt.StateBasedCRDT.{PropagateChanges, StateChanged}

import scala.collection.mutable

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
abstract class StateBasedCRDT[T] extends RepCRDT[T] {

	protected[crdt] def initialState : T
	protected var state : T = initialState


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


		case PropagateChanges =>
			otherReplicas.values.foreach(rep => rep ! StateChanged(replicaId, state))

		case StateChanged(id, otherState : T@unchecked) =>
			merge(otherState)


		case _ => super.receive

	}
}

object StateBasedCRDT {
	case class StateChanged[T](id : ReplicaId, newState : T)
	case object PropagateChanges
}


