package de.tuda.stg.consys.core.legacy

/**
	* Created on 14.02.19.
	*
	* @author Mirko Köhler
	*/

sealed trait ConsistencyLabel extends Serializable

object ConsistencyLabel {

	case object Inconsistent extends ConsistencyLabel
	case object Weak extends ConsistencyLabel
	case object Eventual extends ConsistencyLabel
	case object Causal extends ConsistencyLabel
	case object Strong extends ConsistencyLabel
	case object Local extends ConsistencyLabel

	/* Experimental */
	case object High extends ConsistencyLabel
	case object Low extends ConsistencyLabel

	/* CRDTs */
	case object CvRDT extends ConsistencyLabel
	case object CmRDT extends ConsistencyLabel


	case class Cassandra(replicas : Int) extends ConsistencyLabel


}
