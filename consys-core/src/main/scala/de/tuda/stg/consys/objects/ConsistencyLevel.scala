package de.tuda.stg.consys.objects

/**
	* Created on 14.02.19.
	*
	* @author Mirko Köhler
	*/

sealed trait ConsistencyLevel extends Serializable

object ConsistencyLevel {

	case object Inconsistent extends ConsistencyLevel
	case object Weak extends ConsistencyLevel
	case object Eventual extends ConsistencyLevel
	case object Causal extends ConsistencyLevel
	case object Strong extends ConsistencyLevel
	case object Local extends ConsistencyLevel

	/* Experimental */
	case object High extends ConsistencyLevel
	case object Low extends ConsistencyLevel


}
