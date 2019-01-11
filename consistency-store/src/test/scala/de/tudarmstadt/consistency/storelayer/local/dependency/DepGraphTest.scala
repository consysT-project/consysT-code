package de.tudarmstadt.consistency.storelayer.local.dependency

import org.junit.{Assert, Test}

/**
	* Created on 11.01.19.
	*
	* @author Mirko Köhler
	*/
class DepGraphTest {


	@Test
	def graphTest1(): Unit = {
		val graph = new DepGraph[Int, Symbol, Double, Int]

		graph.addOp(1, 'x, 1.32)
		graph.addOp(2, 'y, 1.00, deps = Seq(1))
		graph.addOp(3, 'x, 2.453, deps = Seq(2))
		graph.addOp(4, 'x, 3.222, deps = Seq(2, 5))

		Assert.assertEquals(Set(5), graph.unresolvedDependencies(4))

		graph.addOp(5, 'x, 5.555)

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
	}

	@Test
	def graphTest2(): Unit = {
		val graph = new DepGraph[Int, Symbol, Double, Int]

		graph.addOp(1, 'x, 1.32)
		graph.addOp(2, 'y, 1.00, deps = Seq(1))
		graph.addOp(3, 'x, 2.453, deps = Seq(2))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(3))

		graph.removeOp(1)

		Assert.assertEquals(Set(1), graph.unresolvedDependencies(3))
	}
}
