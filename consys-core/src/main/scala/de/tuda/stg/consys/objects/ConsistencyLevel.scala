package de.tuda.stg.consys.objects

/**
	* Created on 14.02.19.
	*
	* @author Mirko Köhler
	*/

sealed trait ConsistencyLevel extends Serializable

object ConsistencyLevel {

	@SerialVersionUID(639383L)
	case object Inconsistent extends ConsistencyLevel
	@SerialVersionUID(639384L)
	case object Weak extends ConsistencyLevel
	@SerialVersionUID(639385L)
	case object Eventual extends ConsistencyLevel
	@SerialVersionUID(639386L)
	case object Causal extends ConsistencyLevel
	@SerialVersionUID(639387L)
	case object Strong extends ConsistencyLevel
	@SerialVersionUID(639388L)
	case object Local extends ConsistencyLevel

	/* Experimental */
	case object High extends ConsistencyLevel
	case object Low extends ConsistencyLevel


}
