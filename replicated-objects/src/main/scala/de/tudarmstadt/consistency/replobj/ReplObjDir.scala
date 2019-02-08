package de.tudarmstadt.consistency.replobj

import de.tudarmstadt.consistency.replobj.actors.R

import scala.collection.mutable

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
class ReplObjDir {

	private val index : mutable.Map[Symbol, R[_]] = mutable.HashMap.empty

}
