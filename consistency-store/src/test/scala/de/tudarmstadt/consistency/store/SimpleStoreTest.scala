package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

import org.junit.Assert._

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait SimpleStoreTest {

	type Id = Integer
	type Key = String
	type Data = String

	//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
	protected val store  = Stores.Simple.newTestStore(LocalCluster, initialize = true)


	def assertUpdate(id : Id, key : Key, data : Data, txid : Option[Id], deps : Set[UpdateRef[Id, Key]])(actual : Option[Update[Id, Key, Data]]): Unit = {
		assertEquals(Some(Update(id, key, data, txid.map(TxRef(_)), deps)), actual)
	}

}
