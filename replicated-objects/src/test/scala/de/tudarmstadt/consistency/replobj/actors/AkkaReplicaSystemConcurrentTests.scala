package de.tudarmstadt.consistency.replobj.actors

import java.util.concurrent.{Executors, TimeUnit}

import de.tudarmstadt.consistency.replobj.ConsistencyLevel.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.Ref
import de.tudarmstadt.consistency.replobj.actors.Data.{A, B, C}
import org.scalatest.fixture

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutorService, Future}
import scala.util.{Failure, Random, Success}

/**
	* Created on 10.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemConcurrentTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testTransactionOnSingleMasterObject") { F =>
		F(0).replicate("c", C(
				F(0).replicate("a1", A(100), Strong),
				F(1).replicate("a2", A(200), Strong)),
			Strong)

		concurrent (F) { i =>
			val refC = F(i).ref[C]("c", Strong)
			for (j <- 1 to 100) {
				refC.invoke[Unit]("change", Random.nextInt())
				val (i1, i2) = refC.invoke[(Int, Int)]("get")
				assert(i1 == i2)
			}
		}
	}




	test("testTransactionOnDoubleObjects") { F =>

		val refA1 = F(0).replicate("a1", A(100), Strong)
		val refA2 = F(0).replicate("a2", A(200), Strong)

		F(0).replicate("c1", C(refA1, refA2),	Strong)
		F(0).replicate("c2", C(refA1, refA2), Strong)

		concurrent(F) { i =>
			val refC = if (Random.nextBoolean()) F(i).ref[C]("c1", Strong) else F(i).ref[C]("c2", Strong)
			for (j <- 1 to 100) {
				refC.invoke[Unit]("change", Random.nextInt())
				val (i1, i2) = refC.invoke[(Int, Int)]("get")
				assert(i1 == i2)
			}
		}

	}




}
