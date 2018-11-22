package de.tudarmstadt.consistency.store.objects

/**
	* Created on 21.11.18.
	*
	* @author Mirko Köhler
	*/
object PropagationConsistencyDef {

	trait ConsistencyLevel
	case object Inconsistent extends ConsistencyLevel
	case object MonotonicReads extends ConsistencyLevel
	case object MonotonicWrites extends ConsistencyLevel
	case object Causal extends ConsistencyLevel
	case object Sequential extends ConsistencyLevel
	case object Linearizable extends ConsistencyLevel
	case object Local extends ConsistencyLevel


	object PropagationConsistencyLattice extends ConsistencyLattice[ConsistencyLevel] {
		override def top : ConsistencyLevel = Inconsistent
		override def bot : ConsistencyLevel = Local

		override def intersect(c1 : ConsistencyLevel, c2 : ConsistencyLevel) : ConsistencyLevel = {
			if (c1 < c2)
				c1
			else if (c2 < c1)
				c2
			else if (c1 == c2)
				c1
			else
				Causal
		}

		override def union(c1 : ConsistencyLevel, c2 : ConsistencyLevel) : ConsistencyLevel = {
			if (c1 < c2)
				c2
			else if (c2 < c1)
				c1
			else if (c1 == c2)
				c1
			else
				Inconsistent
		}

		override def smallerEq(c1 : ConsistencyLevel, c2 : ConsistencyLevel) : Boolean = (c1, c2) match {
			case (Local, _) => true
			case (_, Local) => false

			case (Linearizable, _) => true
			case (_, Linearizable) => false

			case (Sequential, _) => true
			case (_, Sequential) => false

			case (Causal, _) => true
			case (_, Causal) => false

			case (MonotonicReads, MonotonicWrites) => false
			case (MonotonicReads, _) => true
			case (MonotonicWrites, MonotonicReads) => false
			case (MonotonicWrites, _) => true
			case (_, MonotonicWrites) => false
			case (_, MonotonicReads) => false

			case _ => true
		}
	}
}


