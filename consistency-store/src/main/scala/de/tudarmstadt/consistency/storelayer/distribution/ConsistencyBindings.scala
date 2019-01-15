package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait ConsistencyBindings[Consistency] {
	self : SessionService[_, _, _, _, _, _, Consistency] =>

	val Consistency: ConsistencyOps

	trait ConsistencyOps {
		def INCONSISTENT : Consistency
		def CAUSAL : Consistency
		def WEAK : Consistency
		def LOCAL : Consistency
	}
}
