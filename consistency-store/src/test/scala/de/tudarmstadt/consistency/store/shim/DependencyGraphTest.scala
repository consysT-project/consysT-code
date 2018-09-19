package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}
import org.junit.Assert.assertEquals

/**
	* Created on 07.09.18.
	*
	* @author Mirko Köhler
	*/
trait DependencyGraphTest {

	type Id = Int
	type Key = Symbol
	type Data = String

	var graph : DependencyGraph[Id, Key, Data] = new DependencyGraph[Id, Key, Data]


	protected def assertResolved(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*)(x : Resolved[Update[Id, Key, Data], EventRef[Id, Key]]): Unit = {
		val upd = Update(id, key, data, txid, deps : _*)
		assertEquals(Found(Some(upd), upd, Set.empty), x)
	}

	protected def assertUnresolvedLatest(resolvedId : Id, resolvedKey : Key, resolvedData : Data, resolvedTxid : Option[Id], resolvedDeps : (Id, Key)*)
	                                  (latestId : Id, latestKey : Key, latestData : Data, latestTxid : Option[Id], latestDeps : (Id, Key)*)
	                                  (unresolvedEvents : EventRef[Id, Key]*)(x : Resolved[Update[Id, Key, Data], EventRef[Id, Key]]): Unit = {

		val resolvedUpd = Update(resolvedId, resolvedKey, resolvedData, resolvedTxid, resolvedDeps : _*)
		val latestUpd = Update(latestId, latestKey, latestData, latestTxid, latestDeps : _*)

		assertEquals(Found(Some(resolvedUpd), latestUpd, unresolvedEvents.toSet), x)
	}

	protected def assertUnresolved(latestId : Id, latestKey : Key, latestData : Data, latestTxid : Option[Id], latestDeps : (Id, Key)*)
	                            (unresolvedEvents : EventRef[Id, Key]*)(x : Resolved[Update[Id, Key, Data], EventRef[Id, Key]]): Unit = {

		val latestUpd = Update(latestId, latestKey, latestData, latestTxid, latestDeps : _*)
		assertEquals(Found(None, latestUpd, unresolvedEvents.toSet), x)
	}

	protected def assertNotFound(x : Resolved[Update[Id, Key, Data], EventRef[Id, Key]]): Unit = {
		assertEquals(NotFound(), x)
	}

}
