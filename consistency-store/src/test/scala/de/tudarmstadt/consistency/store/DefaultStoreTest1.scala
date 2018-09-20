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
			session.startTransaction(IsolationLevels.SI) { tx =>
				tx.write("x", toByteBuffer("Hallo"), ConsistencyLevels.CAUSAL)
				tx.write("y", toByteBuffer("Welt"), ConsistencyLevels.CAUSAL)
				Some()
			}

			//Combine multiple reads
			session.startTransaction(IsolationLevels.SI) { tx =>
				val x = tx.read("x", ConsistencyLevels.CAUSAL)
				val y = tx.read("y", ConsistencyLevels.CAUSAL)

				assertUpdate("x", "Hallo")(x)
				assertUpdate("y", "Welt", "x")(y)
				Some()
			}
		}

		store.close()
	}

}
