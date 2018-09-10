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


	private def assertReadResolved(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*): Unit = {
		val upd = Update(id, key, data, txid, deps : _*)
		assertEquals(Found(Some(upd), upd, Set.empty), sessionOrder.resolve(key))
	}

	private def assertReadNotFound(key : Key): Unit = {
		assertEquals(NotFound(), sessionOrder.resolve(key))
	}

	@Test
	def testSessionOrderConfirmUpdate(): Unit = {
		sessionOrder.lockUpdate(0, 'x, "Hallo")
		sessionOrder.confirmUpdate()
	}

	@Test
	def testSessionOrderReleaseUpdate(): Unit = {
		sessionOrder.lockUpdate(0, 'x, "Hallo")
		sessionOrder.releaseUpdate()
	}

	@Test
	def testSessionOrderCommitTx(): Unit = {
		sessionOrder.startTransaction(0)

		sessionOrder.lockUpdate(1, 'x, "Hallo")
		sessionOrder.confirmUpdate()

		sessionOrder.lockTransaction()
		sessionOrder.commitTransaction()
	}

	@Test
	def testSessionOrderAbortTx(): Unit = {
		sessionOrder.startTransaction(0)

		sessionOrder.lockUpdate(1, 'x, "Hallo")
		sessionOrder.confirmUpdate()

		sessionOrder.lockTransaction()
		sessionOrder.abortTransaction()
	}

	@Test
	def testSessionOrderReadConfirmed() : Unit = {

		assertReadNotFound('x)
		assertReadNotFound('y)

		sessionOrder.addUpdate(0, 'x, "Hallo")
		sessionOrder.addUpdate(1, 'y, "Bonjour")

		assertReadResolved(0, 'x, "Hallo", None)
		assertReadResolved(1, 'y, "Bonjour", None, (0, 'x))
		assertReadNotFound('z)

		sessionOrder.addRead(0, 'x)
		sessionOrder.addUpdate(2, 'z, "Hola")

		assertReadResolved(2, 'z, "Hola", None, (0, 'x), (1, 'y))
	}

	@Test
	def testSessionOrderReadReleased() : Unit = {

		assertReadNotFound('x)
		assertReadNotFound('y)

		sessionOrder.lockUpdate(0, 'x, "Hallo")
		sessionOrder.confirmUpdate()
		sessionOrder.lockUpdate(1, 'y, "Bonjour")
		sessionOrder.releaseUpdate()
		sessionOrder.lockUpdate(2, 'z, "Ciao")
		sessionOrder.confirmUpdate()

		assertReadResolved(0, 'x, "Hallo", None)
		assertReadNotFound('y)
		assertReadResolved(2, 'z, "Ciao", None, (0, 'x))
	}

	@Test
	def testSessionOrderCommitTransactions() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.addUpdate(2, 'y, "Bonjour")
		assertReadResolved(0, 'x, "Hallo", None)
		assertReadResolved(2, 'y, "Bonjour", Some(1), (0, 'x))
		sessionOrder.lockTransaction()
		sessionOrder.commitTransaction()

		assertReadResolved(2, 'y, "Bonjour", Some(1), (0, 'x))
	}

	@Test
	def testSessionOrderCommitTransactionsWithRelease() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.lockUpdate(2, 'y, "Bonjour")
		sessionOrder.releaseUpdate()
		assertReadResolved(0, 'x, "Hallo", None)
		assertReadNotFound('y)
		sessionOrder.lockTransaction()
		sessionOrder.commitTransaction()

		assertReadNotFound('y)
	}


	@Test
	def testSessionOrderAbortTransactions() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.addUpdate(2, 'y, "Bonjour")
		assertReadResolved(0, 'x, "Hallo", None)
		assertReadResolved(2, 'y, "Bonjour", Some(1), (0, 'x))
		sessionOrder.lockTransaction()
		sessionOrder.abortTransaction()

		assertReadNotFound('y)

		sessionOrder.addUpdate(3, 'y, "Bonjour")
		assertReadResolved(3, 'y, "Bonjour", None, (0, 'x))
	}


	@Test(expected = classOf[IllegalStateException])
	def testReleaseNoUpdate(): Unit = {
		sessionOrder.releaseUpdate()
	}

	@Test(expected = classOf[IllegalStateException])
	def testLockNoTx(): Unit = {
		sessionOrder.lockTransaction()
	}

	@Test(expected = classOf[IllegalStateException])
	def testCommitNoTx(): Unit = {
		sessionOrder.startTransaction(0)
		sessionOrder.commitTransaction()
	}

	@Test(expected = classOf[IllegalStateException])
	def testAbortNoTx(): Unit = {
		sessionOrder.startTransaction(0)
		sessionOrder.abortTransaction()
	}


	@Test
	def testSessionOrderMultipleTransactions() : Unit = {
		sessionOrder.addUpdate(0, 'x, "Hallo")

		//Commit a transaction
		sessionOrder.startTransaction(1)
		sessionOrder.addUpdate(2, 'y, "Bonjour")
		sessionOrder.lockAndCommitTransaction()

		sessionOrder.startTransaction(3)
		sessionOrder.addUpdate(4, 'y, "Hola")
		sessionOrder.lockAndAbortTransaction()

		assertReadResolved(0, 'x, "Hallo", None)
		assertReadResolved(2, 'y, "Bonjour", Some(1), (0, 'x))

		sessionOrder.addUpdate(5, 'y, "Ciao")

		assertReadResolved(5, 'y, "Ciao", None, (2, 'y))

		sessionOrder.startTransaction(6)
		sessionOrder.addUpdate(7, 'x, "Konichiwa")
		sessionOrder.addUpdate(8, 'y, "Hello")
		sessionOrder.lockAndCommitTransaction()

		assertReadResolved(7, 'x, "Konichiwa", Some(6), (5, 'y))
		assertReadResolved(8, 'y, "Hello", Some(6), (7, 'x))

		sessionOrder.lockUpdate(9, 'x, "Moin")
		sessionOrder.releaseUpdate()

		sessionOrder.startTransaction(10)
		sessionOrder.addUpdate(11, 'y, "Gude")
		sessionOrder.lockAndAbortTransaction()

		assertReadResolved(7, 'x, "Konichiwa", Some(6), (5, 'y))
		assertReadResolved(8, 'y, "Hello", Some(6), (7, 'x))

	}




}
