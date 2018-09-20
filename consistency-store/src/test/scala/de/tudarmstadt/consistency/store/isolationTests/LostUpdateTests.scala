package de.tudarmstadt.consistency.store.isolationTests

import de.tudarmstadt.consistency.store.SimpleStoreTest
import de.tudarmstadt.consistency.utils.Log
import org.junit.Assert._
import org.junit.Test

/**
	* Created on 18.09.18.
	*
	* @author Mirko Köhler
	*/
trait LostUpdateTests extends SimpleStoreTest.Multi[Int] {

	def isolationValue : Isolation

	def runLostUpdateCommit(consistencyLevel : Consistency): Unit = {
		val baseStore = stores(0)
		val concurrentStore1 = stores(1)
		val concurrentStore2 = stores(2)

		baseStore.startSession { session =>
				session.startTransaction(isolationValue) { tx =>
					tx.write("alice", 1000, consistencyLevel)

					Some ()
				}
		}

		//Wait to make sure that the update did propagate
		Thread.sleep(500)

		val fut1 = parallelSession(concurrentStore1) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.read("alice", consistencyLevel) match {
					case None =>
						//no update propagated yet
						Log.err(classOf[LostUpdateTests], "fut1: could not read any update")
						None
					case Some(v) =>
						Thread.sleep(300)
						tx.write("alice", v + 300, consistencyLevel)
						Some ()
				}
			}
		}

		val fut2 = parallelSession(concurrentStore2) { session =>
			session.startTransaction(isolationValue) { tx =>
				tx.read("alice", consistencyLevel) match {
					case None =>
						//no update propagated yet
						Log.err(classOf[LostUpdateTests], "fut2: could not read any update")
						None
					case Some(v) =>
						Thread.sleep(300)
						tx.write("alice", v + 200, consistencyLevel)
						Some ()
				}
			}
		}

		val results = barrier(fut1, fut2)

		Thread.sleep(100)

		baseStore.startSession { session =>
			session.startTransaction(isolationValue) { tx =>
				(results(0), results(1)) match {
					case (None, None) =>
						//TODO: Can we somehow ensure that at least one transaction commits?
						assertEquals("when no transaction commits, then the value should not change", Some(1000), tx.read("alice", consistencyLevel))
					case (Some(()), None) =>
						assertEquals("only one update should be visible", Some(1300), tx.read("alice", consistencyLevel))
					case (None, Some(())) =>
						assertEquals("only one update should be visible", Some(1200), tx.read("alice", consistencyLevel))
					case (Some(()), Some(())) =>
						assertEquals("both updates should be visible", Some(1500), 	tx.read("alice", consistencyLevel))
				}

				Log.info(classOf[LostUpdateTests], s"transaction info : ${results(0)}, ${results(1)}")

				Some ()
			}
		}
	}

	@Test
	def testLostUpdateCausal(): Unit = {
		runLostUpdateCommit(stores(0).ConsistencyLevels.CAUSAL)
	}

	@Test
	def testLostUpdateWeak(): Unit = {
		runLostUpdateCommit(stores(0).ConsistencyLevels.WEAK)
	}

	@Test
	def testLostUpdateRepeatedly(): Unit = {
		for (i <- 0 to 15) {
			resetStores()
			runLostUpdateCommit(stores(0).ConsistencyLevels.CAUSAL)
		}

	}


}
