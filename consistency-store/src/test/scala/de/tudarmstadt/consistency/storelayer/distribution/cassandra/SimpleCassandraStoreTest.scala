package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import de.tudarmstadt.consistency.storelayer.distribution.cassandra
import de.tudarmstadt.consistency.storelayer.distribution.cassandra.CassandraBinding.{DefaultCassandraStore, SimpleCassandraStore}
import org.junit.{Assert, Before, Test}

/**
	* Created on 15.01.19.
	*
	* @author Mirko Köhler
	*/
class SimpleCassandraStoreTest {

	val store : SimpleCassandraStore = new SimpleCassandraStore

	@Before
	def setupStore(): Unit = {
		store.initialize(reset = true)
	}

	import store._

	private def assertOpRow(id : Int, key : String, data : Double, txid : Option[TxRef], deps : Set[OpRef],
	                        txStatus : String, isolation : String, consistency : String,
	                        actual : OpRow): Unit = {
		Assert.assertEquals(id, actual.id)
		Assert.assertEquals(key, actual.key)
		Assert.assertEquals(data, actual.data, 0.125)
		Assert.assertEquals(txid, actual.txid)
		Assert.assertEquals(deps, actual.deps)
		Assert.assertEquals(txStatus, actual.txStatus)
		Assert.assertEquals(isolation, actual.isolation)
		Assert.assertEquals(consistency, actual.consistency)
	}

	private def assertOpRow(id : Int, key : String, data : Double, txid : Option[TxRef], deps : Set[OpRef],
	                        txStatus : String, isolation : String, consistency : String,
	                        actual : Option[OpRow]): Unit = {
		Assert.assertNotEquals(None, actual)
		assertOpRow(id, key, data, txid, deps, txStatus, isolation, consistency, actual.get)
	}

	@Test
	def testWriteAndRead(): Unit = {
		writeData(1, "x", 32.01, None, Set.empty, TxStatus.COMMITTED, Isolation.NONE, Consistency.INCONSISTENT)
		writeData(2, "y", -41.54, Some(101), Set.empty, TxStatus.PENDING, Isolation.NONE, Consistency.LOCAL)


		//wait to let the update propagate through the store
		Thread.sleep(500)

		assertOpRow(1, "x", 32.01, None, Set.empty[OpRef], TxStatus.COMMITTED, Isolation.NONE, Consistency.INCONSISTENT,
			readData(1, "x")
		)
		assertOpRow(2, "y", -41.54, Some(ref(101)), Set.empty[OpRef], TxStatus.PENDING, Isolation.NONE, Consistency.LOCAL,
			readData(2, "y")
		)
	}



}
