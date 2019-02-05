package de.tudarmstadt.consistency.replobj

import scala.collection.mutable

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
class ReplObjDir {

	private val index : mutable.Map[Symbol, ReplObj[_]] = mutable.HashMap.empty

}
