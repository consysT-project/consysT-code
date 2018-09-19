package de.tudarmstadt.consistency.store

import org.junit.Test

/**
	* Created on 11.09.18.
	*
	* @author Mirko Köhler
	*/
class DefaultStoreTest1 extends DefaultStoreTest {



	@Test
	def singleSession(): Unit = {
		val store = this.store
		import store._

		startSession { session =>

			//Commit a transaction
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				tx.write("x", toByteBuffer("Hallo"), consistencyLevels.causal)
				tx.write("y", toByteBuffer("Welt"), consistencyLevels.causal)
				Some()
			}

			//Combine multiple reads
			session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
				val x = tx.read("x", consistencyLevels.causal)
				val y = tx.read("y", consistencyLevels.causal)

				assertUpdate("x", "Hallo")(x)
				assertUpdate("y", "Welt", "x")(y)
				Some()
			}
		}

		store.close()
	}

}
