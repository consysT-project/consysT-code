package de.tudarmstadt.consistency.store.shim

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
		graph.addUpdate(0, 'x, "Hello", None, Set.empty)
		graph.addUpdate(1, 'y, "World", None, Set(UpdateRef(0, 'x), UpdateRef(3, 'z)))
		graph.addUpdate(2, 'x, "Hi", None, Set(UpdateRef(1, 'y)))

		assertEquals(Set.empty,	graph.unresolvedDependenciesOf(UpdateRef(0, 'x)))
		assertEquals(Set(UpdateRef(3, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(1, 'y)))
		assertEquals(Set(UpdateRef(3, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(2, 'x)))
	}

	@Test
	def unresolvedDependenciesTx(): Unit = {
		graph.addUpdate(0, 'x, "Hello", Some(TxRef(4)), Set.empty)
		graph.addUpdate(1, 'y, "World", Some(TxRef(3)), Set(UpdateRef(0, 'x), UpdateRef(6, 'z)))
		graph.addUpdate(2, 'x, "Hi", Some(TxRef(3)), Set(UpdateRef(1, 'y)))
		graph.addTx(3, Set(UpdateRef(1, 'y), UpdateRef(2, 'x), UpdateRef(5, 'z)))

		assertEquals(Set(TxRef(4)),	graph.unresolvedDependenciesOf(UpdateRef(0, 'x)))
		assertEquals(Set(TxRef(4), UpdateRef(6, 'z), UpdateRef(5, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(1, 'y)))
		assertEquals(Set(TxRef(4), UpdateRef(6, 'z), UpdateRef(5, 'z)),	graph.unresolvedDependenciesOf(UpdateRef(2, 'x)))
	}


}
