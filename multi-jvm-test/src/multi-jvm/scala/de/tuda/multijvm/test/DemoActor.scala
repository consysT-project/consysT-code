package de.tuda.multijvm.test

import akka.actor.Actor

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
class DemoActor extends Actor {

	override def receive : Receive = {
		case n : Int => println(self + " :: " + n)
	}

}
