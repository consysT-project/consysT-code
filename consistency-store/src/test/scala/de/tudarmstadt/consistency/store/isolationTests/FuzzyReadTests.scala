package de.tudarmstadt.consistency.store.isolationTests

import de.tudarmstadt.consistency.store.SimpleStoreTest
import org.junit.Assert._
import org.junit.Test

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
trait FuzzyReadTests extends SimpleStoreTest.Multi[Int] {

	def isolationValue : Isolation

	def runFuzzyReadCommit(consistencyLevel : Consistency): Unit = {
		val baseStore = stores(0)
		val testStore = stores(1)
		val concurrentStore = stores(2)


		val fut1 = parallelSession(concurrentStore) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1000, consistencyLevel)
				tx.update("bob", 1000, consistencyLevel)
				Some ()
			}

			Thread.sleep(600)

			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1500, consistencyLevel)
				tx.read("alice", consistencyLevel)
				tx.update("bob", 1500, consistencyLevel)
				Some ()
			}


		}

		val fut2 = parallelSession(testStore) { session =>
			Thread.sleep(300)

			session.startTransaction(isolationValue) { tx =>
				val a1 = tx.read("alice", consistencyLevel)
				assertEquals("the initial update is visible", Some(1000), a1)

				Thread.sleep(600)

				val a2 = tx.read("alice", consistencyLevel)
				val b2 = tx.read("bob", consistencyLevel)
				assertEquals("the read state did change", Some(1000), a2)
				assertEquals("the newer transaction cannot be visible at all", Some(1000), b2)


				Some ()
			}
		}

		barrier(fut1, fut2)
	}



	def runFuzzyReadStress(consistencyLevel : Consistency): Unit = {
		val baseStore = stores(0)
		val testStore = stores(1)
		val concurrentStore = stores(2)


		val fut1 = parallelSession(concurrentStore) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1000, consistencyLevel)
				Some ()
			}
			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1500, consistencyLevel)
				Some ()
			}
		}

		val fut2 = parallelSession(testStore) { session =>

			session.startTransaction(isolationValue) { tx =>
				val a1 = tx.read("alice", consistencyLevel)

				val a2 = tx.read("alice", consistencyLevel)

				assertTrue(s"the read state cannot change, but was $a1 at first and is now $a2", a1 == a2)

				Some ()
			}
		}

		barrier(fut1, fut2)
	}

	def runFuzzyReadAbort(consistencyLevel : Consistency): Unit = {
		val baseStore = stores(0)
		val testStore = stores(1)
		val concurrentStore = stores(2)


		val fut1 = parallelSession(concurrentStore) { session =>
			// ts 0
			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1000, consistencyLevel)
				Some ()
			}

			Thread.sleep(600)

			// ts 600
			session.startTransaction(isolationValue) { tx =>
				tx.update("alice", 1500, consistencyLevel)
				None
			}


		}

		val fut2 = parallelSession(testStore) { session =>
			Thread.sleep(300)

			// ts 300
			session.startTransaction(isolationValue) { tx =>
				val a1 = tx.read("alice", consistencyLevel)
				assertEquals("the initial update is visible", Some(1000), a1)

				Thread.sleep(600)

				// ts 900
				val a2 = tx.read("alice", consistencyLevel)
				assertEquals("the read state did not change", Some(1000), a2)

				Some ()
			}
		}

		barrier(fut1, fut2)
	}

	@Test
	def testFuzzyReadCommitCausal(): Unit = {
		runFuzzyReadCommit(stores(0).consistencyLevels.causal)
	}

	@Test
	def testFuzzyReadCommitWeak(): Unit = {
		runFuzzyReadCommit(stores(0).consistencyLevels.weak)
	}

	@Test
	def testFuzzyReadAbortCausal(): Unit = {
		runFuzzyReadAbort(stores(0).consistencyLevels.causal)
	}

	@Test
	def testFuzzyReadAbortWeak(): Unit = {
		runFuzzyReadAbort(stores(0).consistencyLevels.weak)
	}

	@Test
	def testFuzzyReadRepeatedly(): Unit = {
		for (i <- 0 to 15) {
			resetStores()
			runFuzzyReadStress(stores(0).consistencyLevels.causal)
		}
	}

}
