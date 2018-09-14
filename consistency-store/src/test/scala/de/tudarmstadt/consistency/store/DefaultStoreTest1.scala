package de.tudarmstadt.consistency.store

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, ObjectInputStream, ObjectOutputStream}
import java.nio.ByteBuffer

import de.tudarmstadt.consistency.store.shim.Event.Update
import org.junit.Assert._
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
				tx.update("x", toByteBuffer("Hallo"), consistencyLevels.causal)
				tx.update("y", toByteBuffer("Welt"), consistencyLevels.causal)
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
