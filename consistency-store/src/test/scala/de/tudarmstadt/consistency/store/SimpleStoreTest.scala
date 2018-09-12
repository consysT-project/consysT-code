package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.Assert._
import org.junit.Before

import scala.reflect.runtime.universe._

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
abstract class SimpleStoreTest[Data : TypeTag] {

	type Id = Integer
	type Key = String
	type TxStatus = String
	type Isolation = String
	type Consistency = String




	def assertUpdate(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*)(actual : Option[Update[Id, Key, Data]]): Unit = {
		assertEquals(Some(Update(id, key, data, txid, deps : _*)), actual)
	}

}
