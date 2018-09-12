package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.{LocalCluster, LocalClusterNode1, LocalClusterNode2, LocalClusterNode3}
import de.tudarmstadt.consistency.store.Store.ITxContext
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.Assert._
import org.junit.{Before, Test}

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}

/**
	* Created on 05.09.18.
	*
	* @author Mirko Köhler
	*/
class SimpleMultiStoreTest extends SimpleStoreTest[Integer] {


	//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
	protected var stores : Seq[SysnameVersionedStore[Id, Key, Integer, TxStatus, Isolation, Consistency, Option[Integer]]]  = null

	@Before
	def setup(): Unit = {

		val idOps = Stores.Simple.createSeqIds

		stores = Seq(
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps, initialize = true),
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps),
			Stores.Simple.newStore[Integer](LocalClusterNode2, idOps = idOps),
			Stores.Simple.newStore[Integer](LocalClusterNode3, idOps = idOps)
		)
	}

	private def transfer(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(from : Key, to : Key, amount : Int) : Unit = {
		(tx.read(from, consistencyLevel), tx.read(to, consistencyLevel)) match {
			case (Some(a), Some(b)) =>
				tx.update(from, a - amount, consistencyLevel)
				tx.update(to, b + amount, consistencyLevel)
			case _ =>
		}
	}

	private def parallelSession[U](
		store : SysnameVersionedStore[Id, Key, Integer, TxStatus, Isolation, Consistency, Option[Integer]]
	)(
		session : (SysnameVersionedStore[Id, Key, Integer, TxStatus, Isolation, Consistency, Option[Integer]], store.SessionCtx) => U
	)(implicit execCtx : ExecutionContext): Future[U] = {
		//Parallel
		val fut : Future[U] = Future {
			import store._
			val u = startSession { sess =>
				//Commit a transaction
				session(store, sess)
			}
//			store.close()
			u
		} recover {
			case e  =>
				e.printStackTrace(System.out)
				fail(e.getMessage)
				null.asInstanceOf[U]
		}
		fut
	}

	@Test
	def testMultipleSessions(): Unit = {
		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		val store = stores(0)

		store.startSession { session =>
			import store._
			//Commit a transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.update("alice", 1000, consistencyLevels.causal)
				tx.update("bob", 1000, consistencyLevels.causal)
				tx.update("carol", 1000, consistencyLevels.causal)
				Some()
			}
		}

		//Parallel
		val future1 = parallelSession(stores(1)) { (store, session) =>
			//Commit a transaction
			val tx1 = session.startTransaction(store.isolationLevels.snapshotIsolation) { tx =>
				transfer(tx, store.consistencyLevels.causal)("alice", "bob", 200)
				Some ()
			}
			println(s"future 1, tx1 $tx1")
		}

		val future2 = parallelSession(stores(2)) { (store, session) =>
			//Commit a transaction
			val tx1 = session.startTransaction(store.isolationLevels.snapshotIsolation) { tx =>
				transfer(tx, store.consistencyLevels.causal)("alice", "carol", 300)
				Some ()
			}
			println(s"future 2, tx1 $tx1")
		}

		val future3 = parallelSession(stores(3)) { (store, session) =>
			//Commit a transaction
			val tx1 = session.startTransaction(store.isolationLevels.snapshotIsolation) { tx =>
				transfer(tx, store.consistencyLevels.causal)("alice", "carol", 50)
				Some ()
			}
			println(s"future 3, tx1 $tx1")
		}

		Await.result(future1, Duration.Inf)
		Await.result(future2, Duration.Inf)
		Await.result(future3, Duration.Inf)


		//Sequential
		store.startSession { session =>
			import store._

			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val a = tx.read("alice", consistencyLevels.causal)
				val b = tx.read("bob", consistencyLevels.causal)
				val c = tx.read("carol", consistencyLevels.causal)

				(a, b, c) match {
					case (Some(aVal), Some(bVal), Some(cVal)) =>
						assertEquals("after money transfer the sum can not change", 3000, aVal + bVal + cVal)
					case t =>
						fail(s"not all reads could be resolved: $t")
				}
				Some ()
			}
		}
	}

	@Test
	def testMultipleSessionRepeatedly(): Unit = {
		for (i <- 0 to 15) testMultipleSessions()
	}

	@Test
	def testReadWriteConflict(): Unit = {
		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		val store = stores(0)
		store.startSession { session =>
			import store._
			//Commit a transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.update("alice", 1000, consistencyLevels.causal)
				tx.update("bob", 0, consistencyLevels.causal)
				tx.update("carol", 0, consistencyLevels.causal)
				Some()
			}
		}

		//Parallel
		val future1 = parallelSession(stores(1)) { (store, session) =>
			//Commit a transaction
			val tx1 = session.startTransaction(store.isolationLevels.snapshotIsolation) { tx =>
				tx.read("alice", store.consistencyLevels.causal) match {
					case Some(a) =>
						Thread.sleep(1000) //<- Wait to let the other transaction finish between reading and writing
						tx.update("alice", a - 200, store.consistencyLevels.causal)
						tx.update("bob", 200, store.consistencyLevels.causal)
					case _ =>
				}
				Some ()
			}
			println(s"future 1, tx1 $tx1")
		}

		val future2 = parallelSession(stores(2)) { (store, session) =>
			Thread.sleep(300) //<- Make sure that the read from the other tx has been processed

			//Commit a transaction
			val tx1 = session.startTransaction(store.isolationLevels.snapshotIsolation) { tx =>
				transfer(tx, store.consistencyLevels.causal)("alice", "carol", 300)
				Some ()
			}
			println(s"future 2, tx1 $tx1")
		}

		Await.result(future1, Duration.Inf)
		Await.result(future2, Duration.Inf)

		//Sequential
		store.startSession { session =>
			import store._
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val a = tx.read("alice", consistencyLevels.causal)
				val b = tx.read("bob", consistencyLevels.causal)
				val c = tx.read("carol", consistencyLevels.causal)
				(a, b, c) match {
					case (Some(aVal), Some(bVal), Some(cVal)) =>
						assertEquals(s"after money transfer the sum can not change. alice = $aVal, bob = $bVal, carol = $cVal", 1000, aVal + bVal + cVal)
					case t =>
						fail(s"not all reads could be resolved: $t")
				}
				Some ()
			}
		}

	}







}
