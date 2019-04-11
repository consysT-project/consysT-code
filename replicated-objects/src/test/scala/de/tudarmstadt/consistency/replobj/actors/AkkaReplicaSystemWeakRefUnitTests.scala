package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Weak
import de.tudarmstadt.consistency.replobj.Ref
import de.tudarmstadt.consistency.replobj.actors.Data.A
import org.scalatest.fixture

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemWeakRefUnitTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4 //Needs to be at least 2

	private val initialField : Int = 3

	override def populate(replica : AkkaReplicaSystem[String], index : Int) : Unit = index match {
		case 0 =>	replica.replicate("a", A(initialField), Weak)
		case _ =>
	}

	private def testWeak(fixture : F, replicaIndex : Int)(expectedFld : Int, expectedReturn : Any)(f : Ref[String, A] => Any) : Unit = {
		val refs = fixture.refs[A]("a", Weak)

		val result = f(refs(replicaIndex))

		assertResult(expectedReturn)(result)

		refs.zipWithIndex.foreach { t =>
			val (ref, index) = t
			if (index == replicaIndex) {
				assertResult(expectedFld) { ref.getField("i")	}
			}	else {
				assertResult(initialField) { ref.getField("i")	}
			}
		}


		//Need to sync ref that produced the changes
		refs(replicaIndex).sync()

		refs.foreach { ref =>
			//Need to sync follower with the master if necessary.
			ref.sync()
			assertResult(expectedFld) { ref.getField("i")	}
		}
	}

	test("testWeakUpdateMaster") { F =>
		testWeak(F, 0)(55, ()) {
			ref => ref.update("i", 55)
		}
	}

	test("testWeakUpdateFollower") { F =>
		testWeak(F, 1)(55, ()) {
			ref => ref.update("i", 55)
		}
	}


	test("testWeakIncMaster") { F =>
		testWeak(F, 0)(4, ()) {
			ref => ref.invoke[Unit]("inc")
		}
	}

	test("testWeakIncFollower") { F =>
		testWeak(F, 1)(4, ()) {
			ref => ref.invoke[Unit]("inc")
		}
	}

	test("testWeakIncAndGetMaster") { F =>
		testWeak(F, 0)(4, 4)(ref => ref.invoke[Int]("incAndGet"))
	}

	test("testWeakIncAndGetFollower") { F =>
		testWeak(F, 1)(4, 4)(ref => ref.invoke[Int]("incAndGet"))
	}

	test("testWeakIncByMaster") { F =>
		testWeak(F, 0)(45, ())(ref => ref.invoke[Unit]("incBy", 42))
	}

	test("testWeakIncByFollower") { F =>
		testWeak(F, 1)(45, ())(ref => ref.invoke[Unit]("incBy", 42))
	}

	test("testWeakIncByAndGetMaster") { F =>
		testWeak(F, 0)(125, 125)(ref => ref.invoke[Int]("incByAndGet", 122))
	}

	test("testWeakIncByAndGetFollower") { F =>
		testWeak(F, 1)(125, 125)(ref => ref.invoke[Int]("incByAndGet", 122))
	}

}



