package de.tudarmstadt.consistency.storelayer.local.dependency
import de.tudarmstadt.consistency.storelayer.distribution.SessionService

/**
	* Created on 15.01.19.
	*
	* @author Mirko Köhler
	*/
class SessionTests {

	val store : SessionService[Int, Int, Symbol, Double, _, _, _] =
		new SessionService[Int, Int, Symbol, Double, Int, Int, Int] {}

	val session : Session[Int, Symbol, Double, Int] = new Session[Int, Symbol, Double, Int] {
		override protected val store : SessionService[Int, Int, Symbol, Double, _, _, _] =
			SessionTests.this.store
	}

}
