package de.tuda.stg.consys.objects.actors

import de.tuda.stg.consys.objects.ConsistencyLevel.Strong
import de.tuda.stg.consys.objects.actors.Data.A
import org.scalatest.fixture

import scala.concurrent.duration.Duration
import scala.util.Random

/**
 * Created on 25.09.19.
 *
 * @author Mirko Köhler
 */
class BarrierTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testBarrier") { F =>
		concurrent (F) { i =>
			Thread.sleep(Random.nextInt(8000)+ 1000)
			println(s"Sleep done on $i")
			F.replicas(i).barrier("test", Duration(12, "s"))
			println(s"Barrier on $i")

		}
	}
}
