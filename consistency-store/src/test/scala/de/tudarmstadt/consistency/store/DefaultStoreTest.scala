package de.tudarmstadt.consistency.store

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, ObjectInputStream, ObjectOutputStream}
import java.nio.ByteBuffer
import java.util.UUID

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.Assert._
import org.junit.Before

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait DefaultStoreTest {

	type Id = UUID
	type Key = String
	type Data = ByteBuffer
	type TxStatus = Int
	type Isolation = Int
	type Consistency = Int

	//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
	protected var store : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]]  = null

	@Before
	def setup(): Unit = {
		store = Stores.Default.newTestStore(LocalCluster, initialize = true)
	}

	protected def toByteBuffer(obj : AnyRef): ByteBuffer = {
		val bos = new ByteArrayOutputStream
		val oos = new ObjectOutputStream(bos)

		//Transform object into a string representation
		oos.writeObject(obj)
		oos.flush()

		val res = ByteBuffer.wrap(bos.toByteArray)
		oos.close()
		res
	}

	protected def fromByteBuffer(bb : ByteBuffer) : AnyRef = {
		val bis = new ByteArrayInputStream(bb.array())
		val ois = new ObjectInputStream(bis)

		val res = ois.readObject
		ois.close()
		res
	}

	def assertUpdate(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*)(actual : Option[Update[Id, Key, Data]]): Unit = {
		assertEquals(Some(Update(id, key, data, txid, deps : _*)), actual)
	}

	def assertUpdate(key : Key, data : AnyRef, deps : Key*)(actual : Option[Update[Id, Key, Data]]): Unit = actual match {
		case Some(Update(_, updKey, updData, _, updDeps)) =>
			assertTrue(updKey == key && fromByteBuffer(updData) == data && deps.toSet == updDeps.map(ref => ref.key))
		case _ =>
			fail()
	}

}
