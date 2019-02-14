package de.tudarmstadt.consistency.replobj.actors

/**
	* Created on 14.02.19.
	*
	* @author Mirko Köhler
	*/
object ConsistencyLevels {

	sealed trait ConsistencyLevel
	sealed trait Inconsistent extends ConsistencyLevel
	sealed trait Weak extends ConsistencyLevel
	sealed trait Eventual extends ConsistencyLevel
	sealed trait Causal extends ConsistencyLevel
	sealed trait Strong extends ConsistencyLevel
	sealed trait Local extends ConsistencyLevel

}
