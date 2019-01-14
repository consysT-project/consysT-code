package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.local.dependency.DepGraph.Op
import org.junit.{Assert, Test}

/**
	* Created on 14.01.19.
	*
	* @author Mirko Köhler
	*/
class SessionTest {


	@Test
	def simpleSessionTest(): Unit = {
		val session = new Session[Int, Symbol, Double, Int] {}

		session.lockUpdate(1, 'x, 3.0)
		session.confirmUpdate()

		session.lockUpdate(2, 'y, 5.2)
		session.confirmUpdate()

		session.lockUpdate(3, 'z, -1.2)
		session.confirmUpdate()

		Assert.assertEquals("no transaction started", None, session.getCurrentTxid)
		Assert.assertEquals("next update depends on last one", Set(3), session.getNextDependencies)


		Assert.assertEquals(Set.empty, session.graph.getDependencies(1))
		Assert.assertEquals(Set(1), session.graph.getDependencies(2))
		Assert.assertEquals(Set(2), session.graph.getDependencies(3))

		Assert.assertEquals(Op(1, 'x, 3.0), session.graph.getOp(1))
		Assert.assertEquals(Op(2, 'y, 5.2), session.graph.getOp(2))
		Assert.assertEquals(Op(3, 'z, -1.2), session.graph.getOp(3))
	}


	@Test
	def transactionTest(): Unit = {
		val session = new Session[Int, Symbol, Double, Int] {}

		session.lockUpdate(1, 'x, 3.0)
		session.confirmUpdate()

		session.lockUpdate(2, 'y, 5.2)
		session.confirmUpdate()

		session.lockUpdate(3, 'z, -1.2)
		session.confirmUpdate()

		Assert.assertEquals("no transaction started", None, session.getCurrentTxid)
		Assert.assertEquals("next update depends on last one", Set(3), session.getNextDependencies)


		Assert.assertEquals(Set.empty, session.graph.getDependencies(1))
		Assert.assertEquals(Set(1), session.graph.getDependencies(2))
		Assert.assertEquals(Set(2), session.graph.getDependencies(3))

		Assert.assertEquals(Op(1, 'x, 3.0), session.graph.getOp(1))
		Assert.assertEquals(Op(2, 'y, 5.2), session.graph.getOp(2))
		Assert.assertEquals(Op(3, 'z, -1.2), session.graph.getOp(3))
	}

}
