package de.tuda.stg.consys.objects.actors

import de.tuda.stg.consys.objects.ConsistencyLevel.Strong
import de.tuda.stg.consys.objects.Ref
import de.tuda.stg.consys.objects.ConsistencyLevel.{Strong, Weak}
import de.tuda.stg.consys.objects.Ref
import de.tuda.stg.consys.objects.actors.Data.A
import org.scalatest.fixture

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/
class AkkaReplicaSystemStrongRefUnitTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
	override def numOfReplicas : Int = 4 //Needs to be at least 2

	override def populate(replica : AkkaReplicaSystem[String], index : Int) : Unit = index match {
		case 0 =>	replica.replicate("a", A(3), Strong)
		case _ =>
	}

	private def testStrong(fixture : F)(expectedFld : Int, expectedReturn : Any)(f : Seq[Ref[String, A]] => Any) : Unit = {
		val refs = fixture.refs[A]("a", Strong)

		val result = f(refs)

		assertResult(expectedReturn)(result)

		refs.foreach { ref =>
			assertResult(expectedFld) { ref.getField("i")	}
		}
	}

	test("testStrongUpdateMaster") { F =>
		testStrong(F)(55, ()) {
			refs => refs(0).update("i", 55)
		}
	}

	test("testStrongUpdateFollower") { F =>
		testStrong(F)(55, ()) {
			refs => refs(1).update("i", 55)
		}
	}


	test("testStrongIncMaster") { F =>
		testStrong(F)(4, ()) {
			refs => refs(0).invoke[Unit]("inc")
		}
	}

	test("testStrongIncFollower") { F =>
		testStrong(F)(4, ()) {
			refs => refs(1).invoke[Unit]("inc")
		}
	}

	test("testStrongIncAndGetMaster") { F =>
		testStrong(F)(4, 4)(refs => refs(0).invoke[Int]("incAndGet"))
	}

	test("testStrongIncAndGetFollower") { F =>
		testStrong(F)(4, 4)(refs => refs(1).invoke[Int]("incAndGet"))
	}

	test("testStrongIncByMaster") { F =>
		testStrong(F)(45, ())(refs => refs(0).invoke[Unit]("incBy", 42))
	}

	test("testStrongIncByFollower") { F =>
		testStrong(F)(45, ())(refs => refs(1).invoke[Unit]("incBy", 42))
	}

	test("testStrongIncByAndGetMaster") { F =>
		testStrong(F)(125, 125)(refs => refs(0).invoke[Int]("incByAndGet", 122))
	}

	test("testStrongIncByAndGetFollower") { F =>
		testStrong(F)(125, 125)(refs => refs(1).invoke[Int]("incByAndGet", 122))
	}


}


