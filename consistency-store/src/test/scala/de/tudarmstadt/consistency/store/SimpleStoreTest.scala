package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.Assert._
import org.junit.Before

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait SimpleStoreTest {

	type Id = Integer
	type Key = String
	type Data = String
	type TxStatus = String
	type Isolation = String
	type Consistency = String

	//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
	protected var store : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]]  = null

	@Before
	def setup(): Unit = {
		store = Stores.Simple.newTestStore(LocalCluster, initialize = true)
	}


	def assertUpdate(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*)(actual : Option[Update[Id, Key, Data]]): Unit = {
		assertEquals(Some(Update(id, key, data, txid, deps : _*)), actual)
	}

}
