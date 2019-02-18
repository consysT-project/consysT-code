package de.tudarmstadt.consistency.multinode.schema

import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak
import de.tudarmstadt.consistency.replobj.Ref

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
@SerialVersionUID(932632L)
class B(var a : Ref[A, Weak]) extends Serializable {
	var x : Int = 0

	def incAndGet() : Int = {
		a <= "inc"
		a[Int]("f") + x
	}
}
