package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.ConsistencyLabel.{Strong, Weak}
import de.tuda.stg.consys.core.legacy.Ref
import de.tuda.stg.consys.core.legacy.akka.Data.{A, B}
import org.scalatest.fixture

/**
	* Created on 10.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemNestedTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testStrongMasterWithStrongNested") { F =>
		val replica0 = F(0)

		val refA1 = replica0.replicate("a1", A(100), Strong)
		val refA2 = replica0.replicate("a2", A(200), Strong)
		val refB : Ref[String, B] = replica0.replicate("b", B(refA1, refA2), Strong)

		val result = refB.invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { F(0).lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { F(1).lookup[A]("a2", Strong).getField("i") }
		}
	}

	test("testStrongFollowerWithStrongNested") { F =>
		val replica0 = F(0)

		val refA1 = replica0.replicate("a1", A(100), Strong)
		val refA2 = replica0.replicate("a2", A(200), Strong)
		val refB : Ref[String, B] = replica0.replicate("b", B(refA1, refA2), Strong)

		val result = F(1).lookup[B]("b", Strong).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { F(0).lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { F(1).lookup[A]("a2", Strong).getField("i") }
		}
	}


	test("testWeakMasterWithStrongNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Strong),
			replica0.replicate("a2", A(200), Strong)),
			Weak)

		val result = F(0).lookup("b", Weak).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			assertResult(104) { replica.lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Strong).getField("i") }
		}

		F(0).lookup("b", Weak).syncAll() //Synchronize the method invocation

		F.replicas.foreach { replica =>
			replica.lookup[B]("b", Weak).sync()
			assertResult(104) { replica.lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Strong).getField("i") }
		}
	}


	test("testWeakFollowerWithStrongNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Strong),
			replica0.replicate("a2", A(200), Strong)),
			Weak)

		val result = F(1).lookup("b", Weak).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Strong).getField("i") }
		}

		F(1).lookup("b", Weak).sync()

		F.replicas.foreach {replica =>
			replica.lookup[B]("b", Weak).sync()
			assertResult(104) { replica.lookup[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Strong).getField("i") }
		}
	}


	test("testStrongWithWeakNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Weak),
			replica0.replicate("a2", A(200), Weak)),
			Strong)

		val result = F(1).lookup[B]("b", Strong).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.lookup("a1", Weak).getField("i") }
				assertResult(202) { replica.lookup("a2", Weak).getField("i") }
			} else {
				assertResult(100) { replica.lookup("a1", Weak).getField("i") }
				assertResult(200) { replica.lookup("a2", Weak).getField("i") }
			}
		}

		F(1).lookup[B]("b", Strong).syncAll()

		F.replicas.foreach {replica =>
			replica.lookup("a1", Weak).sync()
			replica.lookup("a2", Weak).sync()
			assertResult(104) { replica.lookup("a1", Weak).getField("i") }
			assertResult(202) { replica.lookup("a2", Weak).getField("i") }
		}
	}


	test("testWeakWithWeakNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Weak),
			replica0.replicate("a2", A(200), Weak)),
			Weak)

		val result = F(1).lookup[B]("b", Weak).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.lookup("a1", Weak).getField("i") }
				assertResult(202) { replica.lookup("a2", Weak).getField("i") }
			} else {
				assertResult(100) { replica.lookup("a1", Weak).getField("i") }
				assertResult(200) { replica.lookup("a2", Weak).getField("i") }
			}
		}

		F(1).lookup[B]("b", Weak).syncAll()

		F.replicas.zipWithIndex.foreach {replicaWithIndex =>
			val (replica, index) = replicaWithIndex
			replica.lookup("a1", Weak).sync()
			replica.lookup("a2", Weak).sync()
			assertResult(104, "index: " + index) { replica.lookup("a1", Weak).getField("i") }
			assertResult(202, "index: " + index) { replica.lookup("a2", Weak).getField("i") }
		}
	}



}
