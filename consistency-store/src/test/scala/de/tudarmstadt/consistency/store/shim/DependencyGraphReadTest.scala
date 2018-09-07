package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import org.junit.Assert._
import org.junit.Test

/**
	* Created on 07.09.18.
	*
	* @author Mirko Köhler
	*/
class DependencyGraphReadTest extends DependencyGraphTest {

	@Test
	def readNotFound(): Unit = {
		assertNotFound(graph.read('x))
		assertNotFound(graph.read('z))

		graph.add(Update(0, 'x, "Hello", None))

		assertResolved(0, 'x, "Hello", None)(graph.read('x))
		assertNotFound(graph.read('z))
	}

	@Test
	def readUpdatesResolved(): Unit = {
		graph.add(Update(0, 'x, "Hello", None))
		graph.add(Update(1, 'y, "World", None, (0, 'x)))

		assertResolved(0, 'x, "Hello", None)(graph.read('x))
		assertResolved(1, 'y, "World", None, (0, 'x))(graph.read('y))

		graph.add(Update(2, 'x, "Hi", None, (1, 'y)))

		assertResolved(2, 'x, "Hi", None, (1, 'y))(graph.read('x))
		assertResolved(1, 'y, "World", None, (0, 'x))(graph.read('y))
	}

	@Test
	def readUpdatesUnresolved(): Unit = {
		graph.addUpdate(0, 'x, "Hello", None, Set.empty)
		graph.addUpdate(1, 'y, "World", None, Set(UpdateRef(0, 'x), UpdateRef(3, 'z)))
		graph.addUpdate(2, 'x, "Hi", None, Set(UpdateRef(1, 'y)))

		assertUnresolved(1, 'y, "World", None, (0, 'x), (3, 'z))(UpdateRef(3, 'z))(graph.read('y))
		assertUnresolvedLatest(0, 'x, "Hello", None)(2, 'x, "Hi", None, (1, 'y))(UpdateRef(3, 'z))(graph.read('x))

		graph.addUpdate(3, 'z, "!!!", None, Set.empty)

		assertResolved(1, 'y, "World", None, (0, 'x), (3, 'z))(graph.read('y))
		assertResolved(2, 'x, "Hi", None, (1, 'y))(graph.read('x))
		assertResolved(3, 'z, "!!!", None)(graph.read('z))
	}


	@Test
	def readRemoved(): Unit = {
		graph.addUpdate(0, 'x, "Hello", None, Set.empty)
		graph.addUpdate(1, 'y, "World", None, Set(UpdateRef(0, 'x), UpdateRef(3, 'z)))
		graph.addUpdate(2, 'x, "Hi", None, Set(UpdateRef(1, 'y)))

		assertUnresolved(1, 'y, "World", None, (0, 'x), (3, 'z))(UpdateRef(3, 'z))(graph.read('y))
		assertUnresolvedLatest(0, 'x, "Hello", None)(2, 'x, "Hi", None, (1, 'y))(UpdateRef(3, 'z))(graph.read('x))

		assertEquals(Some(Update(1, 'y, "World", None, Set(UpdateRef(0, 'x), UpdateRef(3, 'z)))),
			graph.remove(1))

		assertNotFound(graph.read('y))
		assertUnresolvedLatest(0, 'x, "Hello", None)(2, 'x, "Hi", None, (1, 'y))(UpdateRef(1, 'y))(graph.read('x))

		graph.addUpdate(1, 'y, "Welt", None, Set(UpdateRef(3, 'z)))

		assertEquals(Some(Update(0, 'x, "Hello", None)),
			graph.remove(0))

		assertUnresolved(1, 'y, "Welt", None, (3, 'z)) (UpdateRef(3, 'z)) (graph.read('y))
		assertUnresolved(2, 'x, "Hi", None, (1, 'y)) (UpdateRef(3, 'z)) (graph.read('x))

		graph.addUpdate(3, 'z, "!!!", None, Set.empty)

		assertResolved(1, 'y, "Welt", None, (3, 'z)) (graph.read('y))
		assertResolved(2, 'x, "Hi", None, (1, 'y)) (graph.read('x))
		assertResolved(3, 'z, "!!!", None) (graph.read('z))
	}

	@Test
	def removeNonExisting(): Unit = {
		assertEquals(None,
			graph.remove(0))

		graph.addUpdate(0, 'x, "Hi", None, Set.empty)

		assertEquals(None,
			graph.remove(1))

		assertResolved(0, 'x, "Hi", None)(graph.read('x))
	}

	@Test
	def readCyclicDependency(): Unit = {
		graph.addUpdate(0, 'x, "X", None, Set(UpdateRef(1, 'y)))
		graph.addUpdate(1, 'y, "Y", None, Set(UpdateRef(0, 'x)))

		assertResolved(0, 'x, "X", None, (1, 'y))(graph.read('x))
		assertResolved(1, 'y, "Y", None, (0, 'x))(graph.read('y))
	}

	@Test
	def removeCyclicDependency(): Unit = {
		graph.addUpdate(0, 'x, "X", None, Set(UpdateRef(1, 'y)))
		graph.addUpdate(1, 'y, "Y", None, Set(UpdateRef(2, 'z)))
		graph.addUpdate(2, 'z, "Z", None, Set(UpdateRef(0, 'x)))

		assertResolved(0, 'x, "X", None, (1, 'y))(graph.read('x))
		assertResolved(1, 'y, "Y", None, (2, 'z))(graph.read('y))
		assertResolved(2, 'z, "Z", None, (0, 'x))(graph.read('z))

		graph.remove(2)

		assertUnresolved(0, 'x, "X", None, (1, 'y))(UpdateRef(2, 'z))(graph.read('x))
		assertUnresolved(1, 'y, "Y", None, (2, 'z))(UpdateRef(2, 'z))(graph.read('y))
	}

	@Test(expected = classOf[java.lang.AssertionError])
	def inconsistentUpdate(): Unit = {
		graph.addUpdate(0, 'x, "Hello", None, Set.empty)
		graph.addUpdate(0, 'y, "Welt", None, Set.empty)
	}

	@Test(expected = classOf[java.lang.AssertionError])
	def inconsistentGraph(): Unit = {
		graph.addUpdate(0, 'x, "Hello", Some(TxRef(1)), Set.empty)
		graph.addUpdate(1, 'y, "Welt", None, Set.empty) //TODO: Already find inconsistency here?

		graph.read('x)

	}

	@Test
	def readTxResolved(): Unit = {
		graph.addUpdate(0, 'x, "Hello", Some(TxRef(3)), Set.empty)
		graph.addUpdate(1, 'y, "World", Some(TxRef(3)), Set(UpdateRef(0, 'x)))

		assertUnresolved(0, 'x, "Hello", Some(3))(TxRef(3))(graph.read('x))
		assertUnresolved(1, 'y, "World", Some(3), (0, 'x))(TxRef(3))(graph.read('y))

		assertResolved(0, 'x, "Hello", Some(3))(graph.read('x, Some(TxRef(3))))
		assertResolved(1, 'y, "World", Some(3), (0, 'x))(graph.read('y, Some(TxRef(3))))

		graph.addTx(3, Set(UpdateRef(0, 'x), UpdateRef(1, 'y)))

		assertResolved(0, 'x, "Hello", Some(3))(graph.read('x))
		assertResolved(1, 'y, "World", Some(3), (0, 'x))(graph.read('y))

		graph.remove(0)

		assertNotFound(graph.read('x))
		assertUnresolved(1, 'y, "World", Some(3), (0, 'x))(UpdateRef(0, 'x))(graph.read('y))
	}
	//TODO: Add more tests with transactions...



}
