package de.tudarmstadt.consistency.multinode.schema

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
case class A(var f : Int = 0) {
	def inc(): Unit = f += 1
}
