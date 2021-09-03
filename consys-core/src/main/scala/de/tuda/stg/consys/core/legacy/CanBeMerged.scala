package de.tuda.stg.consys.core.legacy

/**
	* With this trait you *can* mark objects that should be replicated.
	*
	* @author Mirko Köhler
	*/
trait CanBeMerged[T] {
	def merge(other : T) : Unit
}
