package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ConsistencyLevel.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.Ref
import de.tudarmstadt.consistency.replobj.actors.Data.{A, B}
import org.scalatest.fixture

/**
	* Created on 10.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemNestedTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 2

	test("testStrongWithStrongNested") { F =>
		val replica0 = F(0)

		val refA1 = replica0.replicate("a1", A(100), Strong)
		val refA2 = replica0.replicate("a2", A(200), Strong)
		val refB : Ref[String, B] = replica0.replicate("b", B(refA1, refA2), Strong)

		val result = refB.invoke[Int]("incAll")

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.ref[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.ref[A]("a2", Strong).getField("i") }
		}

		println("done.")
	}


	test("testWeakMasterWithStrongNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Strong),
			replica0.replicate("a2", A(200), Strong)),
			Weak)

		val result = F(0).ref("b", Weak).invoke[Int]("incAll")

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			assertResult(104) { replica.ref[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.ref[A]("a2", Strong).getField("i") }
		}

		F(0).ref("b", Weak).syncAll() //Synchronize the method invocation

		F.replicas.foreach { replica =>
			replica.ref[B]("b", Weak).sync()
			assertResult(104) { replica.ref[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.ref[A]("a2", Strong).getField("i") }
		}
	}


	test("testWeakFollowerWithStrongNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Strong),
			replica0.replicate("a2", A(200), Strong)),
			Weak)

		val result = F(1).ref("b", Weak).invoke[Int]("incAll")

		assertResult (104) { result }

		F.replicas.foreach {replica =>
			assertResult(104) { replica.ref[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.ref[A]("a2", Strong).getField("i") }
		}

		F(1).ref("b", Weak).sync()

		F.replicas.foreach {replica =>
			replica.ref[B]("b", Weak).sync()
			assertResult(104) { replica.ref[A]("a1", Strong).getField("i") }
			assertResult(202) { replica.ref[A]("a2", Strong).getField("i") }
		}
	}


	test("testStrongWithWeakNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Weak),
			replica0.replicate("a2", A(200), Weak)),
			Strong)

		val result = F(1).ref[B]("b", Strong).invoke[Int]("incAll")

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.ref("a1", Weak).getField("i") }
				assertResult(202) { replica.ref("a2", Weak).getField("i") }
			} else {
				assertResult(100) { replica.ref("a1", Weak).getField("i") }
				assertResult(200) { replica.ref("a2", Weak).getField("i") }
			}
		}

		F(1).ref[B]("b", Strong).syncAll()

		println("test")

		F.replicas.foreach {replica =>
			replica.ref("a1", Weak).sync()
			replica.ref("a2", Weak).sync()
			assertResult(104) { replica.ref("a1", Weak).getField("i") }
			assertResult(202) { replica.ref("a2", Weak).getField("i") }
		}
	}


	test("testWeakWithWeakNested") { F =>
		val replica0 = F(0)

		replica0.replicate("b", B(
			replica0.replicate("a1", A(100), Weak),
			replica0.replicate("a2", A(200), Weak)),
			Weak)

		val result = F(1).ref[B]("b", Weak).invoke[Int]("incAll")

		assertResult (104) { result }

		F.replicas.foreach { replica =>
			if (replica == F(1)) {
				assertResult(104) { replica.ref("a1", Weak).getField("i") }
				assertResult(202) { replica.ref("a2", Weak).getField("i") }
			} else {
				assertResult(100) { replica.ref("a1", Weak).getField("i") }
				assertResult(200) { replica.ref("a2", Weak).getField("i") }
			}
		}

		F(1).ref[B]("b", Weak).syncAll()

		println("test")

		F.replicas.zipWithIndex.foreach {replicaWithIndex =>
			val (replica, index) = replicaWithIndex
			replica.ref("a1", Weak).sync()
			replica.ref("a2", Weak).sync()
			assertResult(104, "index: " + index) { replica.ref("a1", Weak).getField("i") }
			assertResult(202, "index: " + index) { replica.ref("a2", Weak).getField("i") }
		}
	}



}
