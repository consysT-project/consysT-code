package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}
import org.junit.Assert._
import org.junit.Test

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
class SessionOrderTest {

	type Id = Int
	type Key = Symbol
	type Data = String

	var sessionOrder : SessionOrder[Id, Key, Data] = new SessionOrder[Id, Key, Data]



	private def assertReadResolved(id : Id, key : Key, data : Data, txid : Option[Id], deps : Set[UpdateRef[Id, Key]]): Unit = {
		val upd = Update(id, key, data, txid.map(TxRef(_)), deps)
		assertEquals(Found(Some(upd), upd, Set.empty), sessionOrder.read(key))
	}

	private def assertReadNotFound(key : Key): Unit = {
		assertEquals(NotFound(), sessionOrder.read(key))
	}

	@Test
	def testSessionOrderReads() : Unit = {

		assertReadNotFound('x)
		assertReadNotFound('y)

		sessionOrder.addUpdate(0, 'x, "Hallo")
		sessionOrder.addUpdate(1, 'y, "Bonjour")

		assertReadResolved(0, 'x, "Hallo", None, Set.empty)
		assertReadResolved(1, 'y, "Bonjour", None, Set(UpdateRef(0, 'x)))
		assertReadNotFound('z)

		sessionOrder.addRead(0, 'x)
		sessionOrder.addUpdate(2, 'z, "Hola")

		assertReadResolved(2, 'z, "Hola", None, Set(UpdateRef(0, 'x), UpdateRef(1, 'y)))

	}

	@Test
	def testSessionOrderCommitTransactions() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.addUpdate(2, 'y, "Bonjour")
		assertReadResolved(0, 'x, "Hallo", None, Set.empty)
		assertReadResolved(2, 'y, "Bonjour", Some(1), Set(UpdateRef(0, 'x)))
		sessionOrder.commitTransaction()

		assertReadResolved(2, 'y, "Bonjour", Some(1), Set(UpdateRef(0, 'x)))
	}


	@Test
	def testSessionOrderAbortTransactions() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.addUpdate(2, 'y, "Bonjour")
		assertReadResolved(0, 'x, "Hallo", None, Set.empty)
		assertReadResolved(2, 'y, "Bonjour", Some(1), Set(UpdateRef(0, 'x)))
		sessionOrder.abortTransaction()

		assertReadNotFound('y)

		sessionOrder.addUpdate(3, 'y, "Bonjour")
		assertReadResolved(3, 'y, "Bonjour", Some(1), Set(UpdateRef(0, 'x)))

	}



}
