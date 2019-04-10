package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.Ref

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/
object Data {


	case class A(var i : Int) {

		def inc() : Unit = {
			i += 1
		}

		def incAndGet() : Int = {
			i += 1
			i
		}

		def incBy(amount : Int) : Unit = {
			i += amount
		}

		def incByAndGet(amount : Int) : Int = {
			i += amount
			i
		}
	}


	case class B(a1 : Ref[String, A], a2 : Ref[String, A]) {

		def incAll() : Int = {
			a1.invoke("incByAndGet", 1)
			a2.invoke("incByAndGet", 2)
			a1.invoke("incByAndGet", 3)
		}

	}

}
