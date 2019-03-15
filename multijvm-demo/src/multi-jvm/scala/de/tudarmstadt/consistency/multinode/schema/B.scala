package de.tudarmstadt.consistency.multinode.schema

import de.tudarmstadt.consistency.replobj._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
@SerialVersionUID(932632L)
class B(var a : Ref[String, A]) extends Serializable {
	var x : Int = 0

	def incAndGet : Int = {
		a.invoke("inc")
		a.getField[Int]("f") + x
	}

	override def toString : String =
		s"B(a = $a, x = $x)"
}
