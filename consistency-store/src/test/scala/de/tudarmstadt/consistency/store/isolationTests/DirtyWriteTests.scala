package de.tudarmstadt.consistency.store.isolationTests

import de.tudarmstadt.consistency.store.SimpleStoreTest
import org.junit.Assert.assertTrue
import org.junit.Test

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
trait DirtyWriteTests extends SimpleStoreTest.Multi[Int] {

	def isolationValue : Isolation

	def runDirtyWrite(consistencyLevel : Consistency, useSleeps : Boolean = true): Unit = {
		val testStore = stores(1)
		val concurrentStore1 = stores(2)
		val concurrentStore2 = stores(3)

		val fut1 = parallelSession(concurrentStore1) { session =>
			import concurrentStore1._

			session.startTransaction(isolationLevels.readCommitted) { tx =>
				if (useSleeps) Thread.sleep(500)
				tx.write("alice", 1000, consistencyLevel)
				tx.write("bob", 1000, consistencyLevel)
				if (useSleeps) Thread.sleep(500)

				Some ()
			}
		}

		val fut2 = parallelSession(concurrentStore2) { session =>
			import concurrentStore2._

			session.startTransaction(isolationLevels.readCommitted) { tx =>
				tx.write("alice", 500, consistencyLevel)
				if (useSleeps) Thread.sleep(700)
				tx.write("bob", 500, consistencyLevel)
				if (useSleeps) Thread.sleep(100)

				Some ()
			}
		}

		barrier(fut1, fut2)

		testStore.startSession { session =>
			import testStore._

			session.startTransaction(isolationLevels.readCommitted) { tx =>


				val a = tx.read("alice", consistencyLevel)
				val b = tx.read("alice", consistencyLevel)

				if (useSleeps) assertTrue("alice's update has not been received", a.isDefined)
				if (useSleeps) assertTrue("bob's update has not been received", b.isDefined)

				assertTrue(s"alice and bob's balance should be either both be written by tx1 or by tx2, but got alice = $a, bob = $b", a == b)

				Some ()
			}
		}
	}



	/*Test dirty writes*/
	@Test
	def testDirtyWriteCausal(): Unit = {
		runDirtyWrite(stores(0).consistencyLevels.causal)
	}

	@Test
	def testDirtyWriteWeak(): Unit = {
		runDirtyWrite(stores(0).consistencyLevels.weak)
	}

	@Test
	def testDirtyWritesRepeatedly(): Unit = {
		for (i <- 0 to 15) {
			resetStores()
			runDirtyWrite(stores(0).consistencyLevels.causal, useSleeps = false)
		}
	}

}
