package de.tudarmstadt.consistency.store.isolationTests

import de.tudarmstadt.consistency.store.SimpleStoreTest
import org.junit.Assert.assertEquals
import org.junit.Test

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
trait DirtyReadTests extends SimpleStoreTest.Multi[Int] {

	def isolationValue : Isolation

	def runDirtyReadCommit(consistencyLevel : Consistency): Unit = {
		val testStore1 = stores(1)
		val testStore2 = stores(2)

		val concurrentStore = stores(3)

		val fut1 = parallelSession(concurrentStore) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.write("alice", 1000, consistencyLevel)
				Thread.sleep(1000)

				Some ()
			}
		}

		val fut2 = parallelSession(testStore1) { session =>
			session.startTransaction(isolationValue) { tx =>
				Thread.sleep(500)

				val a1 = tx.read("alice", consistencyLevel)
				assertEquals("the update can not be visible yet", None, a1)

				Some ()
			}
		}

		val fut3 = parallelSession(testStore2) { session =>
			session.startTransaction(isolationValue) { tx =>
				Thread.sleep(1500)

				val a2 = tx.read("alice", consistencyLevel)
				assertEquals("the update has to be visible after the transaction has committed", Some(1000), a2)

				Some ()
			}
		}

		barrier(fut1, fut2, fut3)
	}

	def runDirtyReadAbort(consistencyLevel : Consistency): Unit = {
		val testStore = stores(1)
		val concurrentStore = stores(2)

		val fut1 = parallelSession(concurrentStore) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.write("alice", 1000, consistencyLevel)
				Thread.sleep(1000)
				None
			}
		}

		val fut2 = parallelSession(testStore) { session =>
			session.startTransaction(isolationValue) { tx =>
				Thread.sleep(500)

				val a1 = tx.read("alice", consistencyLevel)
				assertEquals("the update can not be visible yet", None, a1)

				Thread.sleep(700)

				val a2 = tx.read("alice", consistencyLevel)
				assertEquals("the update can not be visible as the transaction has been aborted", None, a2)

				Some ()
			}
		}

		barrier(fut1, fut2)
	}

	/*Test dirty reads*/
	@Test
	def testDirtyReadCommitCausal(): Unit = {
		runDirtyReadCommit(stores(0).ConsistencyLevels.CAUSAL)
	}

	@Test
	def testDirtyReadCommitWeak(): Unit = {
		runDirtyReadCommit(stores(0).ConsistencyLevels.WEAK)
	}

	@Test
	def testDirtyReadAbortCausal(): Unit = {
		runDirtyReadAbort(stores(0).ConsistencyLevels.CAUSAL)
	}

	@Test
	def testDirtyReadAbortWeak(): Unit = {
		runDirtyReadAbort(stores(0).ConsistencyLevels.WEAK)
	}

}
