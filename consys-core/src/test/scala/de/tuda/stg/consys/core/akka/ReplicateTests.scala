package de.tuda.stg.consys.core.akka

import de.tuda.stg.consys.core.ConsistencyLevel.Strong
import de.tuda.stg.consys.core.akka.Data.A
import org.scalatest.fixture

import scala.util.Random

/**
 * Created on 25.09.19.
 *
 * @author Mirko Köhler
 */
class ReplicateTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testWaitingForObject") { F =>
		concurrent (F) { i =>
			if (i == 0) {
				for (j <- 1 to 100) {
					F(i).replicate("a" + j, A(0), Strong)
				}
			} else {
				for (j <- 1 to 100) {
					val refA = F(i).lookup[A]("a" + j, Strong)
					refA.await()
					refA.deref
				}
			}
		}
	}
}
