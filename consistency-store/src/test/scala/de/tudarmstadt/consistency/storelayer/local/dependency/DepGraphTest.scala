package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution.{OpRef, SessionService}
import de.tudarmstadt.consistency.storelayer.local.dependency.DepGraph.Op
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

		Assert.assertEquals(Set(ref(5, 'x)), graph.unresolvedDependencies(ref(4, 'x)))

		graph += (5, 'x, 5.555)

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(ref(4, 'x)))
	}

	@Test
	def dependencyTest2(): Unit = {
		graph += (1, 'x, 1.32)
		graph += (2, 'y, 1.00, (1, 'x))
		graph += (3, 'x, 2.453, (2, 'y))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(ref(3, 'x)))

		graph.removeOp(1)

		Assert.assertEquals(Set(ref(1, 'x)), graph.unresolvedDependencies(ref(3, 'x)))
	}

	@Test
	def transactionTest1(): Unit = {

		val _1 = ref(1, 'x)
		val _2 = ref(2, 'y)
		val _3 = ref(3, 'x)
		val _4 = ref(4, 'x)

		val _100 = ref(100)

		graph += (1, 'x, 1.0, Some(100))
		graph += (2, 'y, 1.0, Some(100), _1)
		graph += (4, 'x, 3.0, _2)

		Assert.assertEquals(Set(_100), graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set(_100), graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set(_100), graph.unresolvedDependencies(_4))

		graph.addTx(100)

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_4))

		graph.addOpsToTx(100, _3)

		Assert.assertEquals(Set(_3), graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set(_3), graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set(_3), graph.unresolvedDependencies(_4))

		graph += (3, 'x, 2.0, Some(100))

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_4))
	}

	@Test
	def transactionTest2(): Unit = {
		val _1 = ref(1, 'x)
		val _2 = ref(2, 'y)
		val _3 = ref(3, 'z)
		val _4 = ref(4, 'x)
		val _5 = ref(5, 'y)

		val _100 = ref(100)

		graph += (1, 'x, 3.2, Some(100))

		Assert.assertEquals(Set(_100), graph.unresolvedDependencies(_1))

		graph.addOpsToTx(100, _1, _2, _3)

		Assert.assertEquals(Set(_2, _3, _100), graph.unresolvedDependencies(_1))

		graph.addTx(100)

		Assert.assertEquals(Set(_2, _3), graph.unresolvedDependencies(_1))

		graph += (2, 'y, 1.2, Some(100), _1)
		graph += (3, 'z, 3.4, Some(100), _2, _4)

		Assert.assertEquals(Set(_4), graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set(_4), graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set(_4), graph.unresolvedDependencies(_3))
		Assert.assertEquals(Set(_4), graph.unresolvedDependencies(_4))

		graph.addOpsToTx(100, _5)

		Assert.assertEquals(Set(_4, _5), graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set(_4, _5), graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set(_4, _5), graph.unresolvedDependencies(_3))
		Assert.assertEquals(Set(_4), graph.unresolvedDependencies(_4))
		Assert.assertEquals(Set(_4, _5), graph.unresolvedDependencies(_5))

		graph += (4, 'x, 4.4)

		Assert.assertEquals(Set(_5), graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set(_5), graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set(_5), graph.unresolvedDependencies(_3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_4))
		Assert.assertEquals(Set(_5), graph.unresolvedDependencies(_5))

		graph += (5, 'y, 7.2, Some(100), _3, _4)

		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_1))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_2))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_3))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_4))
		Assert.assertEquals(Set.empty, graph.unresolvedDependencies(_5))
	}

	@Test
	def testRead1(): Unit = {
		graph += (1, 'x, 4.4)

		Assert.assertEquals(Set(Op(1, 'x, 4.4)), graph.read('x))

		graph += (2, 'x, 3.3)

		Assert.assertEquals(Set(Op(1, 'x, 4.4), Op(2, 'x, 3.3)), graph.read('x))

		graph += (3, 'x, 2.2, (1, 'x), (2, 'x))

		Assert.assertEquals(Set(Op(3, 'x, 2.2)), graph.read('x))

		graph += (4, 'y, 31234, (3, 'x))
		graph += (5, 'x, 1.1, (4, 'y))
		graph += (6, 'x, 7.7, (3, 'x))

		Assert.assertEquals(Set(Op(6, 'x, 7.7), Op(5, 'x, 1.1)), graph.read('x))
	}
}
