package de.tudarmstadt.consistency.replobj

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
trait Replicable extends Serializable {

	def replicated() : Unit
}
