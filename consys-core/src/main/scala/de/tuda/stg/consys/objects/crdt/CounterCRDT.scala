package de.tuda.stg.consys.objects.crdt

import de.tuda.stg.consys.objects.crdt.CRDT.{Accessor, Mutator, ReplicaId}
import de.tuda.stg.consys.objects.crdt.CounterCRDT.{Get, Inc}

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/


object CounterCRDT {

	class OpBased extends OpBasedCRDT[Int](0) {

		override def handleOperation(op : CRDT.Operation) : Option[Any] = op match {
			case Inc =>
				state += 1
				None
			case Get =>
				Some(state)
		}

	}

	class StateBased extends StateBasedCRDT[Map[ReplicaId, Int]] {

		override protected [crdt] def initialState : Map[ReplicaId, ReplicaId] =
			Map.empty.withDefaultValue(0)

		override def handleOperation(op : CRDT.Operation) : Option[Any] = op match {
			case Inc =>
				inc(replicaId)
				None
			case Get =>
				Some(state.values.sum)
		}

		override def merge(otherState : Map[ReplicaId, Int]) : Unit = {
			otherState.foreach(entry =>
				state = state.updated(entry._1, math.max(state(entry._1), entry._2))
			)
		}

		private def inc(id : ReplicaId): Unit =
			state = state.updated(id, state(id) + 1)

	}

	case object Inc extends Mutator
	case object Get extends Accessor
}
