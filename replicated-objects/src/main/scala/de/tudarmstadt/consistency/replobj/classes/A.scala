package de.tudarmstadt.consistency.replobj.classes

import de.tudarmstadt.consistency.replobj.actors.Replicateable

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
case class A(var f : Int = 0) extends Replicateable[A] {
	def inc(): Unit = f += 1

	override def replicate() : A = copy()
}
