package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.ConsistencyLabel.{Strong, Weak}
import de.tuda.stg.consys.core.legacy.Ref
import de.tuda.stg.consys.core.legacy.akka.Data.{A, C}
import de.tuda.stg.consys.core.legacy._
import org.scalatest.fixture

import scala.util.Random

/**
	* Created on 10.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemConcurrentTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testStrongTransactionOnSingleObject") { F =>
		F(0).replicate("c", C(
				F(0).replicate("a1", A(0), Strong),
				F(1).replicate("a2", A(0), Strong)),
			Strong)

		concurrent (F) { i =>
			val refC = F(i).lookup[C]("c", Strong)
			for (j <- 1 to 100) {
				refC <=[Unit]("change", Random.nextInt())
				val (i1, i2) = refC.invoke[(Int, Int)]("get")
				assert(i1 == i2)
			}
		}
	}


	test("testStrongTransactionOnDoubleObjects") { F =>

		val refA1 = F(0).replicate("a1", A(0), Strong)
		val refA2 = F(0).replicate("a2", A(0), Strong)

		F(0).replicate("c1", C(refA1, refA2),	Strong)
		F(0).replicate("c2", C(refA1, refA2), Strong)

		concurrent(F) { i =>
			val refC = if (Random.nextBoolean()) F(i).lookup[C]("c1", Strong) else F(i).lookup[C]("c2", Strong)
			for (j <- 1 to 100) {
				refC <=[Unit]("change", Random.nextInt())
				val (i1, i2) = refC.invoke[(Int, Int)]("get")
				assert(i1 == i2)
			}
		}
	}


	test("testWeakTransactionOnSingleObject") { F =>
		F(0).replicate("c", C(
			F(0).replicate("a1", A(0), Weak),
			F(1).replicate("a2", A(0), Weak)),
			Weak)

		concurrent (F) { i =>
			val refC = F(i).lookup[C]("c", Weak)
			for (j <- 1 to 100) {
				val a1 = refC.getField[Ref[String, A]]("a1")
				val a2 = refC.getField[Ref[String, A]]("a2")
				a1.invoke[Unit]("inc", Seq(Seq()))
				a2.invoke[Unit]("inc", Seq(Seq()))
			}
		}

		//Sync all the changes
		concurrent (F) { i =>
			val refC = F(i).lookup[C]("c", Weak)
			refC.syncAll()
		}
		concurrent (F) { i => //We have to sync twice to have synced all the updates from all sources.
			val refC = F(i).lookup[C]("c", Weak)
			refC.syncAll()
		}

		concurrent (F) { i =>
			val refC = F(i).lookup[C]("c", Weak)
			val (f1, f2) = refC.invoke[(Int, Int)]("get")

			assert(f1 == f2)
			assert(f1 == numOfReplicas * 100)
			assert(f2 == numOfReplicas * 100)
		}
	}


	test("testWeakTransactionOnDoubleObjects") { F =>

		val refA1 = F(0).replicate("a1", A(0), Weak)
		val refA2 = F(0).replicate("a2", A(0), Weak)

		F(0).replicate("c1", C(refA1, refA2),	Weak)
		F(0).replicate("c2", C(refA1, refA2), Weak)

		concurrent(F) { i =>
			val refC = if (Random.nextBoolean()) F(i).lookup[C]("c1", Weak) else F(i).lookup[C]("c2", Weak)

			val a1 = refC.getField[Ref[String, A]]("a1")
			val a2 = refC.getField[Ref[String, A]]("a2")

			for (j <- 1 to 100) {
				a1.invoke[Unit]("inc", Seq(Seq()))
				a2.invoke[Unit]("inc", Seq(Seq()))
			}
		}

		concurrent (F) { i =>
			val refC1 = F(i).lookup[C]("c1", Weak)
			val refC2 = F(i).lookup[C]("c2", Weak)
			refC1.syncAll()
			refC2.syncAll()
		}
		concurrent (F) { i => //We have to sync twice to have synced all the updates from all sources.
			val refC1 = F(i).lookup[C]("c1", Weak)
			val refC2 = F(i).lookup[C]("c2", Weak)
			refC1.syncAll()
			refC2.syncAll()
		}

		concurrent (F) { i =>
			val refC1 = F(i).lookup[C]("c1", Weak)
			val refC2 = F(i).lookup[C]("c2", Weak)
			val (f1, f2) = refC1.invoke[(Int, Int)]("get")
			assert(f1 == f2)
			assert(f1 == numOfReplicas * 100)
			assert(f2 == numOfReplicas * 100)

			val (g1, g2) = refC2.invoke[(Int, Int)]("get")
			assert(g1 == g2)
			assert(g1 == numOfReplicas * 100)
			assert(g2 == numOfReplicas * 100)

		}
	}




}
