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
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", "Hallo", ConsistencyLevels.CAUSAL)
				tx.write("y", "Welt", ConsistencyLevels.CAUSAL)

				Some ()
			}

			//Abort a transaction
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", "Hello", ConsistencyLevels.CAUSAL)
				tx.write("z", "World", ConsistencyLevels.CAUSAL)

				None
			}

			//Read from aborted transaction
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", "Hola", ConsistencyLevels.CAUSAL)
				tx.read("z", ConsistencyLevels.CAUSAL) match {
					case Some(str) => tx.write("z", str + "!!!", ConsistencyLevels.CAUSAL)
					case None => tx.write("z", "Amigos", ConsistencyLevels.CAUSAL)
				}

				Some ()
			}

			//Combine multiple reads
			session.startTransaction(IsolationLevels.SI) { tx =>
				val x = tx.read("x", ConsistencyLevels.CAUSAL)
				val y = tx.read("y", ConsistencyLevels.CAUSAL)
				val z = tx.read("z", ConsistencyLevels.CAUSAL)

				val s = List(x, y, z).flatten.map(upd => upd.data).mkString(" ")
				tx.write("s", s, ConsistencyLevels.CAUSAL)

				Some ()
			}

			//Evaluate current state of the database
			session.startTransaction(IsolationLevels.SI) { tx =>
				val w = tx.read("w", ConsistencyLevels.CAUSAL)
				assertEquals(None, w)

				val x = tx.read("x", ConsistencyLevels.CAUSAL)
				//Note on Id: each update and each transaction increases id by 1
				assertUpdate(
						8, //8, because it is the 8th event: tx -> upd -> upd -> tx -> upd -> upd -> tx -> >UPD<
						"x", //x is the key that is being read
						"Hola", //the data that has been written by this key
						Some(7), //the update is part of the transaction with id 7
						(3, "y") //the dependency (which results from read dependencies and the session dependency)
				)(x)

				val y = tx.read("y", ConsistencyLevels.CAUSAL)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val z = tx.read("z", ConsistencyLevels.CAUSAL)
				assertUpdate(9, "z", "Amigos", Some(7), (8, "x"))(z)

				val s = tx.read("s", ConsistencyLevels.CAUSAL)
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
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", "Hallo", ConsistencyLevels.CAUSAL)
				tx.write("y", "Welt", ConsistencyLevels.CAUSAL)

				Some ()
			}
		}

		println("Session 2")

		startSession { session =>
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", "Hello", ConsistencyLevels.CAUSAL)
				tx.write("z", "World", ConsistencyLevels.CAUSAL)

				Some ()
			}

			session.startTransaction(IsolationLevels.SI) { tx =>
				val w = tx.read("w", ConsistencyLevels.CAUSAL)
				assertEquals(None, w)

				val x = tx.read("x", ConsistencyLevels.CAUSAL)
				assertUpdate(5, "x", "Hello", Some(4))(x)

				val y = tx.read("y", ConsistencyLevels.CAUSAL)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val z = tx.read("z", ConsistencyLevels.CAUSAL)
				assertUpdate(6, "z", "World", Some(4), (5, "x"))(z)

				Some ()
			}
		}

		println("Session 3")

		startSession { session =>
			session.startTransaction(IsolationLevels.SI) { tx =>
				val x = tx.read("x", ConsistencyLevels.CAUSAL)
				assertUpdate(5, "x", "Hello", Some(4))(x)

				val y = tx.read("y", ConsistencyLevels.CAUSAL)
				assertUpdate(3, "y", "Welt", Some(1), (2, "x"))(y)

				val r = List(x, y).flatten.map(upd => upd.data).mkString(" ")
				tx.write("x", r, ConsistencyLevels.CAUSAL)

				val x2 = tx.read("x", ConsistencyLevels.CAUSAL)
				assertUpdate(9, "x", "Hello Welt", Some(8), (5, "x"), (3, "y"))(x2)

				Some ()
			}
		}

		println("Session 4")

		startSession { session =>
			session.startTransaction(IsolationLevels.SI) { tx =>
				//Here we have to resolve the dependencies of the read (9, x) as well, and not just x
				val x2 = tx.read("x", ConsistencyLevels.CAUSAL)
				assertUpdate(9, "x", "Hello Welt", Some(8), (5, "x"), (3, "y"))(x2)

				Some ()
			}
		}

		println("Done.")


		store.close()


	}





}
