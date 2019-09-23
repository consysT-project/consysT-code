package de.tuda.stg.consys.objects.actors

import de.tuda.stg.consys.objects.ConsistencyLevel.{Low, High}
import de.tuda.stg.consys.objects.Ref
import de.tuda.stg.consys.objects.actors.Data.{A, B}
import org.scalatest.fixture

/**
	* Created on 10.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemNestedHighLowTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4

	test("testLowMasterWithLowNested") { F =>
		val replica0 = F(0)

		val refA1 = replica0.replicate("a1", A(100), Low)
		val refA2 = replica0.replicate("a2", A(200), Low)
		val refB : Ref[String, B] = replica0.replicate("b", B(refA1, refA2), Low)

		val result = refB.invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}
	}

	test("testLowFollowerWithLowNested") { F =>
		val replica0 = F(0)

		val refA1 = replica0.replicate("a1", A(100), Low)
		val refA2 = replica0.replicate("a2", A(200), Low)
		val refB : Ref[String, B] = replica0.replicate("b", B(refA1, refA2), Low)

		val result = F(1).lookup[B]("b", Low).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}
	}


	test("testHighMasterWithLowNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Low),
			replica0.replicate("a2", A(200), Low)),
			High)

		val result = F(0).lookup("b", High).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}

		F(0).lookup("b", High).syncAll() //Synchronize the method invocation

		F.replicas.foreach { replica =>
			replica.lookup[B]("b", High).sync()
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}
	}


	test("testHighFollowerWithLowNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Low),
			replica0.replicate("a2", A(200), Low)),
			High)

		val result = F(1).lookup("b", High).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}

		F(1).lookup("b", High).sync()

		F.replicas.foreach {replica =>
			replica.lookup[B]("b", High).sync()
			assertResult(104) { replica.lookup[A]("a1", Low).getField("i") }
			assertResult(202) { replica.lookup[A]("a2", Low).getField("i") }
		}
	}


	test("testLowWithHighNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), High),
			replica0.replicate("a2", A(200), High)),
			Low)

		val result = F(1).lookup[B]("b", Low).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.lookup("a1", High).getField("i") }
				assertResult(202) { replica.lookup("a2", High).getField("i") }
			} else {
				assertResult(104) { replica.lookup("a1", High).getField("i") }
				assertResult(202) { replica.lookup("a2", High).getField("i") }
			}
		}

		F(1).lookup[B]("b", Low).syncAll()

		F.replicas.foreach {replica =>
			assertResult(104) { replica.lookup("a1", High).getField("i") }
			assertResult(202) { replica.lookup("a2", High).getField("i") }
		}
	}


	test("testHighWithHighNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), High),
			replica0.replicate("a2", A(200), High)),
			High)

		val result = F(1).lookup[B]("b", High).invoke[Int]("incAll", Seq(Seq()))

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.lookup("a1", High).getField("i") }
				assertResult(202) { replica.lookup("a2", High).getField("i") }
			} else {
				assertResult(100) { replica.lookup("a1", High).getField("i") }
				assertResult(200) { replica.lookup("a2", High).getField("i") }
			}
		}

		F(1).lookup[B]("b", High).syncAll()

		F.replicas.zipWithIndex.foreach {replicaWithIndex =>
			val (replica, index) = replicaWithIndex
			replica.lookup("a1", High).sync()
			replica.lookup("a2", High).sync()
			assertResult(104, "index: " + index) { replica.lookup("a1", High).getField("i") }
			assertResult(202, "index: " + index) { replica.lookup("a2", High).getField("i") }
		}
	}



}
