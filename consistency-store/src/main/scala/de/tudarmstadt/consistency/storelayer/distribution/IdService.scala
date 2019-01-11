package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait IdService[Id] {
	self : SessionService[Id, _, _, _, _, _] =>

	def freshId() : Id

}
