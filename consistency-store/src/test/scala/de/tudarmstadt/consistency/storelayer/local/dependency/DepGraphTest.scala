package de.tudarmstadt.consistency.storelayer.local.dependency

import org.junit.{Assert, Test}

/**
	* Created on 11.01.19.
	*
	* @author Mirko Köhler
	*/
class DepGraphTest {


	@Test
	def dependencyTest1(): Unit = {
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
	def dependencyTest2(): Unit = {
		val graph = new DepGraph[Int, Symbol, Double, Int]

		graph.addOp(1, 'x, 1.32)
		graph.addOp(2, 'y, 1.00, deps = Seq(1))
		graph.addOp(3, 'x, 2.453, deps = Seq(2))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(3))

		graph.removeOp(1)

		Assert.assertEquals(Set(1), graph.unresolvedDependencies(3))
	}

	@Test
	def transactionTest1(): Unit = {
		val graph = new DepGraph[Int, Symbol, Double, Int]

		graph.addOp(1, 'x, 1.0, Some(100))
		graph.addOp(2, 'y, 1.0, Some(100), Set(1))
		graph.addOp(4, 'x, 3.0, deps = Set(2))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))

		graph.addOpToTx(100, 3)

		Assert.assertEquals(Set(3), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(3), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(3), graph.unresolvedDependencies(4))

		graph.addOp(3, 'x, 2.0, Some(100))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
	}

	@Test
	def transactionTest2(): Unit = {
		val graph = new DepGraph[Int, Symbol, Double, Int]

		graph.addOp(1, 'x, 3.2, Some(100))

//		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))

		graph.addOpToTx(100, 1, 2, 3)

//		Assert.assertEquals(Set(2, 3), graph.unresolvedDependencies(1))

		graph.addOp(2, 'y, 1.2, Some(100), Set(1))
		graph.addOp(3, 'z, 3.4, Some(100), Set(2, 4))

		Assert.assertEquals(Set(4), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(4))

		graph.addOpToTx(100, 5)

		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(4, 5), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set(4), graph.unresolvedDependencies(4))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(5))

		graph.addOp(4, 'x, 4.4)

		Assert.assertEquals(Set(5), graph.unresolvedDependencies(1))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(2))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
		Assert.assertEquals(Set(5), graph.unresolvedDependencies(5))

		graph.addOp(5, 'y, 7.2, Some(100), Set(3, 4))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(4))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(5))
	}
}
