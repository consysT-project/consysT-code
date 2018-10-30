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
class DependencyGraphUnresolvedTest extends DependencyGraphTest {


	@Test
	def unresolvedDependenciesNonTx(): Unit = {
		graph.addUpdate(Update(0, 'x, "Hello", None))
		graph.addUpdate(Update(1, 'y, "World", None, (0, 'x), (3, 'z)))
		graph.addUpdate(Update(2, 'x, "Hi", None, (1, 'y)))

		assertEquals(Set.empty,	graph.unresolvedDependenciesOf(UpdateRef(0, 'x)))
		assertEquals(Set(UpdateRef(3, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(1, 'y)))
		assertEquals(Set(UpdateRef(3, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(2, 'x)))
	}

	@Test
	def unresolvedDependenciesTx(): Unit = {
		graph.addUpdate(Update(0, 'x, "Hello", Some(4)))
		graph.addUpdate(Update(1, 'y, "World", Some(3), (0, 'x), (6, 'z)))
		graph.addUpdate(Update(2, 'x, "Hi", Some(3), (1, 'y)))

		assertEquals(Set(TxRef(4)),	graph.unresolvedDependenciesOf(UpdateRef(0, 'x)))
		assertEquals(Set(TxRef(4), UpdateRef(6, 'z), UpdateRef(5, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(1, 'y)))
		assertEquals(Set(TxRef(4), UpdateRef(6, 'z), UpdateRef(5, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(2, 'x)))
	}


}
