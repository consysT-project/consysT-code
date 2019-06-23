package de.tuda.stg.consys.objects.crdt

import de.tuda.stg.consys.objects.crdt.CRDT.{Accessor, Mutator, ReplicaId}

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/


object AddOnlySetCRDT {


	class StateBased[T] extends StateBasedCRDT[Set[T]] {

		override protected [crdt] def initialState : Set[T] = Set.empty

		override def merge(otherState : Set[T]) : Unit =
			state = state.union(otherState)

		override def handleOperation(op : CRDT.Operation) : Option[Any] = op match {
			case Add(e : T) =>
				state = state + e
				None
			case Contains(e : T) =>
				Some(state.contains(e))
			case Get =>
				Some(state)
		}
	}

	case class Add[T](e : T) extends Mutator
	case class Contains[T](e : T) extends Accessor
	case object Get extends Accessor
}
