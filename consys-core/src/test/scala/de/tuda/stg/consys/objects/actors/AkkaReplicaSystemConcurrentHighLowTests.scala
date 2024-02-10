//package de.tuda.stg.consys.objects.actors
//
//import de.tuda.stg.consys.objects.ConsistencyLevel.{Low, High}
//import de.tuda.stg.consys.objects.Ref
//import de.tuda.stg.consys.objects.actors.Data.{A, C}
//import org.scalatest.fixture
//
//import scala.util.Random
//
///**
//	* Created on 10.04.19.
//	*
//	* @author Mirko Köhler
//	*/
//class AkkaReplicaSystemConcurrentHighLowTests extends fixture.FunSuite with AkkaReplicaSystemSuite {
//	override def numOfReplicas : Int = 4
//
//	test("testLowTransactionOnSingleObject") { F =>
//		F(0).replicate("c", C(
//				F(0).replicate("a1", A(0), Low),
//				F(1).replicate("a2", A(0), Low)),
//			Low)
//
//		concurrent (F) { i =>
//			val refC = F(i).lookup[C]("c", Low)
//			for (j <- 1 to 100) {
//				refC <=[Unit]("change", Random.nextInt())
//				val (i1, i2) = refC.invoke[(Int, Int)]("get")
//				assert(i1 == i2)
//			}
//		}
//	}
//
//
//	test("testLowTransactionOnDoubleObjects") { F =>
//
//		val refA1 = F(0).replicate("a1", A(0), Low)
//		val refA2 = F(0).replicate("a2", A(0), Low)
//
//		F(0).replicate("c1", C(refA1, refA2),	Low)
//		F(0).replicate("c2", C(refA1, refA2), Low)
//
//		concurrent(F) { i =>
//			val refC = if (Random.nextBoolean()) F(i).lookup[C]("c1", Low) else F(i).lookup[C]("c2", Low)
//			for (j <- 1 to 100) {
//				refC <=[Unit]("change", Random.nextInt())
//				val (i1, i2) = refC.invoke[(Int, Int)]("get")
//				assert(i1 == i2)
//			}
//		}
//	}
//
//
//	test("testHighTransactionOnSingleObject") { F =>
//		F(0).replicate("c", C(
//			F(0).replicate("a1", A(0), High),
//			F(1).replicate("a2", A(0), High)),
//			High)
//
//		concurrent (F) { i =>
//			val refC = F(i).lookup[C]("c", High)
//			for (j <- 1 to 100) {
//				val a1 = refC.getField[Ref[String, A]]("a1")
//				val a2 = refC.getField[Ref[String, A]]("a2")
//				a1.invoke[Unit]("inc")
//				a2.invoke[Unit]("inc")
//			}
//		}
//
//		//Sync all the changes
//		concurrent (F) { i =>
//			val refC = F(i).lookup[C]("c", High)
//			refC.syncAll()
//		}
//		concurrent (F) { i => //We have to sync twice to have synced all the updates from all sources.
//			val refC = F(i).lookup[C]("c", High)
//			refC.syncAll()
//		}
//
//		concurrent (F) { i =>
//			val refC = F(i).lookup[C]("c", High)
//			val (f1, f2) = refC.invoke[(Int, Int)]("get")
//
//			assert(f1 == f2)
//			assert(f1 == numOfReplicas * 100)
//			assert(f2 == numOfReplicas * 100)
//		}
//	}
//
//
//	test("testHighTransactionOnDoubleObjects") { F =>
//
//		val refA1 = F(0).replicate("a1", A(0), High)
//		val refA2 = F(0).replicate("a2", A(0), High)
//
//		F(0).replicate("c1", C(refA1, refA2),	High)
//		F(0).replicate("c2", C(refA1, refA2), High)
//
//		concurrent(F) { i =>
//			val refC = if (Random.nextBoolean()) F(i).lookup[C]("c1", High) else F(i).lookup[C]("c2", High)
//
//			val a1 = refC.getField[Ref[String, A]]("a1")
//			val a2 = refC.getField[Ref[String, A]]("a2")
//
//			for (j <- 1 to 100) {
//				a1.invoke[Unit]("inc")
//				a2.invoke[Unit]("inc")
//			}
//		}
//
//		concurrent (F) { i =>
//			val refC1 = F(i).lookup[C]("c1", High)
//			val refC2 = F(i).lookup[C]("c2", High)
//			refC1.syncAll()
//			refC2.syncAll()
//		}
//		concurrent (F) { i => //We have to sync twice to have synced all the updates from all sources.
//			val refC1 = F(i).lookup[C]("c1", High)
//			val refC2 = F(i).lookup[C]("c2", High)
//			refC1.syncAll()
//			refC2.syncAll()
//		}
//
//		concurrent (F) { i =>
//			val refC1 = F(i).lookup[C]("c1", High)
//			val refC2 = F(i).lookup[C]("c2", High)
//			val (f1, f2) = refC1.invoke[(Int, Int)]("get")
//			assert(f1 == f2)
//			assert(f1 == numOfReplicas * 100)
//			assert(f2 == numOfReplicas * 100)
//
//			val (g1, g2) = refC2.invoke[(Int, Int)]("get")
//			assert(g1 == g2)
//			assert(g1 == numOfReplicas * 100)
//			assert(g2 == numOfReplicas * 100)
//
//		}
//	}
//
//
//
//
//}
