package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution.SessionService

/**
	* Created on 15.01.19.
	*
	* @author Mirko Köhler
	*/
class GraphTests {

	val graph : DepGraph[Int, Symbol, Double, Int] = new DepGraph[Int, Symbol, Double, Int] {
		override val store : SessionService[Int, Int, Symbol, Double, _, _, _] =
			new SessionService[Int, Int, Symbol, Double, Int, Int, Int] {}
	}

}
