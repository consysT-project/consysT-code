package de.tudarmstadt.consistency.replobj.classes

import de.tudarmstadt.consistency.replobj.actors.{R, Replicateable}

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
case class B(distA : R[A], locA : A) extends Replicateable[B] {

	def incAll() : Unit = {
		distA.call("inc")
		locA.inc()
		println(distA.call[String]("toString") + " -- " + locA)
	}

	override def replicate() : B = copy()
}
