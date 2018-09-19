package de.tudarmstadt.consistency.store

import org.junit.Assert._
import org.junit.Test

/**
	* Created on 05.09.18.
	*
	* @author Mirko Köhler
	*/
class SimpleSingleStoreTest extends SimpleStoreTest.Single[String] {



	@Test
	def singleSession(): Unit = {
		val store = this.store
		import store._


		startSession { session =>

			//Commit a transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", "Hallo", consistencyLevels.causal)
				tx.write("y", "Welt", consistencyLevels.causal)

				Some ()
			}

			//Abort a transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", "Hello", consistencyLevels.causal)
				tx.write("z", "World", consistencyLevels.causal)

				None
			}

			//Read from aborted transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", "Hola", consistencyLevels.causal)
				tx.read("z", consistencyLevels.causal) match {
					case Some(str) => tx.write("z", str + "!!!", consistencyLevels.causal)
					case None => tx.write("z", "Amigos", consistencyLevels.causal)
				}

				Some ()
			}

			//Combine multiple reads
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val x = tx.read("x", consistencyLevels.causal)
				val y = tx.read("y", consistencyLevels.causal)
				val z = tx.read("z", consistencyLevels.causal)

				val s = List(x, y, z).flatten.map(upd => upd.data).mkString(" ")
				tx.write("s", s, consistencyLevels.causal)

				Some ()
			}

			//Evaluate current state of the database
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val w = tx.read("w", consistencyLevels.causal)
				assertEquals(None, w)

				val x = tx.read("x", consistencyLevels.causal)
				//Note on Id: each update and each transaction increases id by 1
				assertUpdate(
						8, //8, because it is the 8th event: tx -> upd -> upd -> tx -> upd -> upd -> tx -> >UPD<
						"x", //x is the key that is being read
						"Hola", //the data that has been written by this key
						Some(7), //the update is part of the transaction with id 7
						(3, "y") //the dependency (which results from read dependencies and the session dependency)
				)(x)

				val y = tx.read("y", consistencyLevels.causal)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val z = tx.read("z", consistencyLevels.causal)
				assertUpdate(9, "z", "Amigos", Some(7), (8, "x"))(z)

				val s = tx.read("s", consistencyLevels.causal)
				assertUpdate(11, "s", "Hola Welt Amigos", Some(10), (9, "z"), (8, "x"), (3, "y"))(s)

				Some ()
			}

			session.print()
		}

		store.close()
	}

	@Test
	def multiSession(): Unit = {
		val store = this.store
		import store._

		println("Session 1")

		startSession { session =>
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", "Hallo", consistencyLevels.causal)
				tx.write("y", "Welt", consistencyLevels.causal)

				Some ()
			}
		}

		println("Session 2")

		startSession { session =>
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", "Hello", consistencyLevels.causal)
				tx.write("z", "World", consistencyLevels.causal)

				Some ()
			}

			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val w = tx.read("w", consistencyLevels.causal)
				assertEquals(None, w)

				val x = tx.read("x", consistencyLevels.causal)
				assertUpdate(5, "x", "Hello", Some(4))(x)

				val y = tx.read("y", consistencyLevels.causal)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val z = tx.read("z", consistencyLevels.causal)
				assertUpdate(6, "z", "World", Some(4), (5, "x"))(z)

				Some ()
			}
		}

		println("Session 3")

		startSession { session =>
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val x = tx.read("x", consistencyLevels.causal)
				assertUpdate(5, "x", "Hello", Some(4))(x)

				val y = tx.read("y", consistencyLevels.causal)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val r = List(x, y).flatten.map(upd => upd.data).mkString(" ")
				tx.write("x", r, consistencyLevels.causal)

				val x2 = tx.read("x", consistencyLevels.causal)
				assertUpdate(9, "x", "Hello Welt", Some(8), (5, "x"), (3, "y"))(x2)

				Some ()
			}
		}

		println("Session 4")

		startSession { session =>
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				//Here we have to resolve the dependencies of the read (9, x) as well, and not just x
				val x2 = tx.read("x", consistencyLevels.causal)
				assertUpdate(9, "x", "Hello Welt", Some(8), (5, "x"), (3, "y"))(x2)

				Some ()
			}
		}

		println("Done.")


		store.close()


	}





}
