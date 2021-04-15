package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.Ref

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
			a1 <=("incByAndGet", 1)
			a2 <=("incByAndGet", 2)
			a1 <=("incByAndGet", 3)
		}
	}

	case class C(a1 : Ref[String, A], a2 : Ref[String, A]) {
		def change(i : Int) : Unit = {
			a1.setField("i", i)
			Thread.sleep(10)
			a2.setField("i", i)
		}

		def get : (Int, Int) = {
			(a1.getField("i"), a2.getField("i"))
		}
	}

}
