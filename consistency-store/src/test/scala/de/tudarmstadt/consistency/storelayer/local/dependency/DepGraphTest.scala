package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution.{OpRef, SessionService}
import org.junit.{Assert, Test}

/**
	* Created on 11.01.19.
	*
	* @author Mirko Köhler
	*/
class DepGraphTest extends GraphTests {

	import store._

	@Test
	def dependencyTest1(): Unit = {
		graph += (1, 'x, 1.32)
		graph += (2, 'y, 1.00, (1, 'x))
		graph += (3, 'x, 2.453, (2, 'y))
		graph += (4, 'x, 3.222, (2, 'y), (5, 'x))

		Assert.assertEquals(Set(5), graph.unresolvedDependencies(OpRef(4, 'x)))

		graph += (5, 'x, 5.555)

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(OpRef(4, 'x)))
	}

	@Test
	def dependencyTest2(): Unit = {
		graph += (1, 'x, 1.32)
		graph += (2, 'y, 1.00, (1, 'x))
		graph += (3, 'x, 2.453, (2, 'y))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(3))

		graph.removeOp(1)

		Assert.assertEquals(Set(1), graph.unresolvedDependencies(3))
	}

	@Test
	def transactionTest1(): Unit = {
		graph += (1, 'x, 1.0, Some(100))
		graph += (2, 'y, 1.0, Some(100), (1, 'x))
		graph += (4, 'x, 3.0, (2, 'y))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))

		graph.addOpsToTx(100, (3, 'x))

		Assert.assertEquals(Set(3), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(3), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(3), graph.unresolvedDependencies(4))

		graph += (3, 'x, 2.0, Some(100))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
	}

	@Test
	def transactionTest2(): Unit = {
		graph += (1, 'x, 3.2, Some(100))

//		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))

		graph.addOpsToTx(100, (1, 'x), (2, 'y), (3, 'z))

//		Assert.assertEquals(Set(2, 3), graph.unresolvedDependencies(1))

		graph += (2, 'y, 1.2, Some(100), (1, 'x))
		graph += (3, 'z, 3.4, Some(100), (2, 'y), (4, 'x))

		Assert.assertEquals(Set(4), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(4))

		graph.addOpsToTx(100, (5, 'y))

		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(4))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(5))

		graph += (4, 'x, 4.4)

		Assert.assertEquals(Set(5), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(5))

		graph += (5, 'y, 7.2, Some(100), (3, 'z), (4, 'x))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(5))
	}
}
