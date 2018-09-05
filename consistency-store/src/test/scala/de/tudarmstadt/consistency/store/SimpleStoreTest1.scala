package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.shim.Event.{EventRef, Update}
import de.tudarmstadt.consistency.utils.Log
import org.junit.Test
import org.junit.Assert._

/**
	* Created on 05.09.18.
	*
	* @author Mirko Köhler
	*/
class SimpleStoreTest1 {


	@Test
	def singleSession(): Unit = {
		//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
		val store = Stores.Simple.newTestStore(LocalCluster, initialize = true)
		import store._

		startSession { session =>

			//Commit a transaction
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				tx.update("x", "Hallo", consistencyLevelOps.sequential)
				tx.update("y", "Welt", consistencyLevelOps.sequential)
				Some ()
			}

			//Abort a transaction
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				tx.update("x", "Hello", consistencyLevelOps.sequential)
				tx.update("z", "World", consistencyLevelOps.sequential)
				None
			}

			//Read from aborted transaction
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				tx.update("x", "Hola", consistencyLevelOps.sequential)
				tx.read("z", consistencyLevelOps.sequential) match {
					case Some(str) => tx.update("z", str + "!!!", consistencyLevelOps.sequential)
					case None => tx.update("z", "Amigos", consistencyLevelOps.sequential)
				}
				Some ()
			}

			//Combine multiple reads
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				val x = tx.read("x", consistencyLevelOps.sequential)
				val y = tx.read("y", consistencyLevelOps.sequential)
				val z = tx.read("z", consistencyLevelOps.sequential)

				val s = List(x, y, z).flatten.map(upd => upd.data).mkString(" ")
				tx.update("s", s, consistencyLevelOps.sequential)

				Some ()
			}

			//Evaluate current state of the database
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				val w = tx.read("w", consistencyLevelOps.sequential)
				assertEquals(None, w)

				val x = tx.read("x", consistencyLevelOps.sequential)
				//Note on Id: each update and each transaction increases id by 1
				assertEquals(
					Some( //We expect to get a result when reading
						Update(
							8, //8, because it is the 8th event: tx -> upd -> upd -> tx -> upd -> upd -> tx -> >UPD<
							"x", //x is the key that is being read
							"Hola", //the data that has been written by this key
							Some(7), //the update is part of the transaction with id 7
							Set(EventRef(3, "y")) //the dependency (which results from read dependencies and the session dependency)
						)
					), x)

				val y = tx.read("y", consistencyLevelOps.sequential)
				assertEquals(Some(Update(3, "y", "Welt", Some(1), Set(EventRef(2, "x")))), y)

				val z = tx.read("z", consistencyLevelOps.sequential)
				assertEquals(Some(Update(9, "z", "Amigos", Some(7), Set(EventRef(8, "x")))), z)

				val s = tx.read("s", consistencyLevelOps.sequential)
				assertEquals(Some(Update(11, "s", "Hola Welt Amigos", Some(10), Set(EventRef(9, "z"), EventRef(8, "x"), EventRef(3, "y")))), s)

				Some ()
			}

			session.print()
		}

		store.close()
	}

	@Test
	def multiSession(): Unit = {
		//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
		val store = Stores.Simple.newTestStore(LocalCluster, initialize = true)
		import store._

		startSession { session =>
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				tx.update("x", "Hallo", consistencyLevelOps.sequential)
				tx.update("y", "Welt", consistencyLevelOps.sequential)
				Some ()
			}
		}

		startSession { session =>
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				tx.update("x", "Hello", consistencyLevelOps.sequential)
				tx.update("z", "World", consistencyLevelOps.sequential)
				Some ()
			}

			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				val w = tx.read("w", consistencyLevelOps.sequential)
				assertEquals(None, w)

				val x = tx.read("x", consistencyLevelOps.sequential)
				assertEquals(Some(Update[Integer, String, String](5, "x", "Hello", Some(4), Set.empty)), x)

				val y = tx.read("y", consistencyLevelOps.sequential)
				assertEquals(Some(Update(3, "y", "Welt", Some(1), Set(EventRef(2, "x")))), y)

				val z = tx.read("z", consistencyLevelOps.sequential)
				assertEquals(Some(Update(6, "z", "World", Some(4), Set(EventRef(5, "x")))), z)

				Some ()
			}
		}

		startSession { session =>
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				val x = tx.read("x", consistencyLevelOps.sequential)
				assertEquals(Some(Update[Integer, String, String](5, "x", "Hello", Some(4), Set.empty)), x)

				val y = tx.read("y", consistencyLevelOps.sequential)
				assertEquals(Some(Update(3, "y", "Welt", Some(1), Set(EventRef(2, "x")))), y)

				val r = List(x, y).flatten.map(upd => upd.data).mkString(" ")
				tx.update("x", r, consistencyLevelOps.sequential)

				val x2 = tx.read("x", consistencyLevelOps.sequential)
				assertEquals(Some(Update(9, "x", "Hello Welt", Some(8), Set(EventRef(5, "x"), EventRef(3, "y")))), x2)

				Some ()
			}
		}

		startSession { session =>
			session.startTransaction(isolationLevelOps.snapshotIsolation) { tx =>
				val x2 = tx.read("x", consistencyLevelOps.sequential)
				assertEquals(Some(Update(9, "x", "Hello Welt", Some(8), Set(EventRef(5, "x"), EventRef(3, "y")))), x2)

				Some ()
			}
		}

		store.close()

	}



}
