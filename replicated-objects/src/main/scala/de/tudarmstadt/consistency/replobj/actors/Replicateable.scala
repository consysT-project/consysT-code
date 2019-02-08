package de.tudarmstadt.consistency.replobj.actors

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
trait Replicateable[T] {
	def replicate() : T
}
