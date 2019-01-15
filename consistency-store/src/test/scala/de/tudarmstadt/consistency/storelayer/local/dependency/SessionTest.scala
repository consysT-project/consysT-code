package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.local.dependency.DepGraph.Op
import org.junit.{Assert, Test}

/**
	* Created on 14.01.19.
	*
	* @author Mirko Köhler
	*/
class SessionTest extends SessionTests {

	import session.store._

	@Test
	def simpleSessionTest(): Unit = {
		session.lockUpdate(1, 'x, 3.0)
		session.confirmUpdate()

		session.lockUpdate(2, 'y, 5.2)
		session.confirmUpdate()

		session.lockUpdate(3, 'z, -1.2)
		session.confirmUpdate()

		Assert.assertEquals("no transaction started", None, session.getCurrentTxid)
		Assert.assertEquals("next update depends on last one", Set(ref(3, 'z)), session.getNextDependencies)


		Assert.assertEquals(Set.empty, session.graph.getDependencies(1, 'x))
		Assert.assertEquals(Set(ref(1, 'x)), session.graph.getDependencies(2, 'y))
		Assert.assertEquals(Set(ref(2, 'y)), session.graph.getDependencies(3, 'z))

		Assert.assertEquals(Op(1, 'x, 3.0), session.graph.getOp(1))
		Assert.assertEquals(Op(2, 'y, 5.2), session.graph.getOp(2))
		Assert.assertEquals(Op(3, 'z, -1.2), session.graph.getOp(3))
	}


	@Test
	def transactionCommitTest(): Unit = {

		session.startTransaction(100)

		session.lockUpdate(1, 'x, 3.0)
		session.confirmUpdate()

		session.lockUpdate(2, 'y, 5.2)
		session.confirmUpdate()

		session.lockUpdate(3, 'z, -1.2)
		session.confirmUpdate()


		Assert.assertEquals("no transaction started", Some(100), session.getCurrentTxid)

		session.lockAndCommitTransaction()

		Assert.assertEquals("no transaction started", None, session.getCurrentTxid)
		Assert.assertEquals("next update depends on last one", Set(ref(3, 'z)), session.getNextDependencies)


		Assert.assertEquals(Set.empty, session.graph.getDependencies(1, 'x))
		Assert.assertEquals(Set(ref(1, 'x)), session.graph.getDependencies(2, 'y))
		Assert.assertEquals(Set(ref(2, 'y)), session.graph.getDependencies(3, 'z))

		Assert.assertEquals(Op(1, 'x, 3.0), session.graph.getOp(1))
		Assert.assertEquals(Op(2, 'y, 5.2), session.graph.getOp(2))
		Assert.assertEquals(Op(3, 'z, -1.2), session.graph.getOp(3))
	}





	@Test
	def transactionAbortTest(): Unit = {

		session.startTransaction(100)

		session.lockUpdate(1, 'x, 3.0)
		session.confirmUpdate()

		session.lockUpdate(2, 'y, 5.2)
		session.confirmUpdate()

		session.lockUpdate(3, 'z, -1.2)
		session.confirmUpdate()


		Assert.assertEquals("no transaction started", Some(100), session.getCurrentTxid)

		session.lockAndAbortTransaction()

		Assert.assertEquals("no transaction started", None, session.getCurrentTxid)
		Assert.assertEquals("next update depends on last one", Set.empty, session.getNextDependencies)

		def tryGetDependencies(f : => Unit) : Unit = {
			try {
				f
				Assert.fail("expected IllegalArgumentException")
			} catch {
				case e : IllegalArgumentException =>
			}
		}

		def tryGetOp(f : => Unit) : Unit = {
			try {
				f
				Assert.fail("expected IllegalArgumentException")
			} catch {
				case e : NoSuchElementException =>
			}
		}

		tryGetDependencies { session.graph.getDependencies(1, 'x) }
		tryGetDependencies { session.graph.getDependencies(2, 'y) }
		tryGetDependencies { session.graph.getDependencies(3, 'z) }

		tryGetOp { session.graph.getOp(1) }
		tryGetOp { session.graph.getOp(2) }
		tryGetOp { session.graph.getOp(3) }
	}

}
