package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorSystem
import de.tudarmstadt.consistency.replobj.classes.{A, B}

import scala.language.postfixOps

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo {

	def main(args : Array[String]): Unit = {
		implicit val actorSystem : ActorSystem = ActorSystem("repl")
		println(actorSystem.log.isDebugEnabled)


		val a = A()
		val replA : R[A] = R.create(a)
		val replB : R[B] = R.create(B(replA, A()))

		//call methods
		replA <= "inc"
		println(replA <= "toString")
		//get a field
		println(replA("f"))

		//set a field
		replA("f") = 10
		replA.print()

		val replA2 = replA!

		Thread.sleep(3000)

		replA <= "inc"
		replA.print()

		replB.print()
		replB <= "incAll"
		replB.print()

		replA.print()
		println(replA2)



	}

}
