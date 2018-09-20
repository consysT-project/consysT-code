package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.examples.BankingStore
import de.tudarmstadt.consistency.utils.Log
import org.junit.Assert._
import org.junit.Test

import scala.concurrent.ExecutionContext

/**
	* Created on 05.09.18.
	*
	* @author Mirko Köhler
	*/
class MixedIsolationMultiStoreTest extends SimpleStoreTest.Multi[Integer] with BankingStore {

	@Test
	def testReadFromNoneIsolated(): Unit = {
		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		val store = stores(0)

		store.startSession { session =>
			import store._
			//Commit a transaction
			session.startTransaction(IsolationLevels.NONE) { tx =>
				tx.write("alice", 1000, ConsistencyLevels.CAUSAL)
				tx.write("bob", 1000, ConsistencyLevels.CAUSAL)
				tx.write("carol", 1000, ConsistencyLevels.CAUSAL)
				Some()
			}
		}
		//Make sure that the data has been propagated to all replicas
		Thread.sleep(500)

		//Parallel repeatedly updating
		val future0 = parallelSession(store) { session =>
			import store._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.NONE) { tx =>
				for (i <- 1 to 10) {
					tx.write("alice", 1000 + (i * 200), ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
			println(s"future 1, tx1 $tx1")
		}

		//Parallel
		val store1 = stores(1)
		val future1 = parallelSession(store1) { session =>
			import store1._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.NONE) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertTrue(s"expected at least two different reads, but got: $s", s.size > 1)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store2 = stores(2)
		val future2 = parallelSession(store2) { session =>
			import store2._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.RC) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertTrue(s"expected at least two different reads, but got: $s", s.size > 1)
				Some ()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store3 = stores(2)
		val future3 = parallelSession(store3) { session =>
			import store3._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.SI) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"only expected one read in snapshot isolation, but got: $s", 1, s.size)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		barrier(future0, future1, future3, future2)
	}


	@Test
	def testReadFromRC(): Unit = {
		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		val store = stores(0)

		store.startSession { session =>
			import store._
			//Commit a transaction
			session.startTransaction(IsolationLevels.NONE) { tx =>
				tx.write("alice", 1000, ConsistencyLevels.CAUSAL)
				tx.write("bob", 1000, ConsistencyLevels.CAUSAL)
				tx.write("carol", 1000, ConsistencyLevels.CAUSAL)
				Some()
			}
		}
		//Make sure that the data has been propagated to all replicas
		Thread.sleep(500)

		//Parallel repeatedly updating
		val future0 = parallelSession(store) { session =>
			import store._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.RC) { tx =>

				for (i <- 1 to 10) {
					tx.write("alice", 1000 + (i * 200), ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
			println(s"future 1, tx1 $tx1")
		}

		//Parallel
		val store1 = stores(1)
		val future1 = parallelSession(store1) { session =>
			import store1._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.NONE) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"expected two reads in none, but got: $s", 2, s.size)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store2 = stores(2)
		val future2 = parallelSession(store2) { session =>
			import store2._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.RC) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"expected two reads in rc, but got: $s", 2, s.size)
				Some ()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store3 = stores(2)
		val future3 = parallelSession(store3) { session =>
			import store3._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.SI) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"only expected one read in snapshot isolation, but got: $s", 1, s.size)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		barrier(future0, future1, future3, future2)
	}


	@Test
	def testReadFromSI(): Unit = {
		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		val store = stores(0)

		store.startSession { session =>
			import store._
			//Commit a transaction
			session.startTransaction(IsolationLevels.NONE) { tx =>
				tx.write("alice", 1000, ConsistencyLevels.CAUSAL)
				tx.write("bob", 1000, ConsistencyLevels.CAUSAL)
				tx.write("carol", 1000, ConsistencyLevels.CAUSAL)
				Some()
			}
		}
		//Make sure that the data has been propagated to all replicas
		Thread.sleep(500)

		//Parallel repeatedly updating
		val future0 = parallelSession(store) { session =>
			import store._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.SI) { tx =>

				for (i <- 1 to 10) {
					tx.write("alice", 1000 + (i * 200), ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}
				Some()
			}

			assertEquals("the transaction will not commit due to conflicting reads", None, tx1)
			println(s"future 1, tx1 $tx1")
		}

		//Parallel
		val store1 = stores(1)
		val future1 = parallelSession(store1) { session =>
			import store1._
			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.NONE) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"expected always the same read, but got: $s", Set(Some(1000)), s)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store2 = stores(2)
		val future2 = parallelSession(store2) { session =>
			import store2._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.RC) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"expected always the same read, but got: $s", Set(Some(1000)), s)
				Some ()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		val store3 = stores(2)
		val future3 = parallelSession(store3) { session =>
			import store3._

			//Commit a transaction
			val tx1 = session.startTransaction(IsolationLevels.SI) { tx =>
				var s : Set[Option[Integer]] = Set.empty
				for (i <- 1 to 15) {
					s =  s + tx.read("alice", ConsistencyLevels.CAUSAL)
					Thread.sleep(50)
				}

				assertEquals(s"expected always the same read, but got: $s", Set(Some(1000)), s)
				Some()
			}

			assertEquals("the transaction has to commit", Some(), tx1)
		}

		barrier(future0, future1, future2, future3)
	}




}
