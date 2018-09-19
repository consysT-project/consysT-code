package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.cassandra.ConnectionParams.{LocalCluster, LocalClusterNode1, LocalClusterNode2, LocalClusterNode3}
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.Assert._
import org.junit.Before

import scala.concurrent.{Await, ExecutionContext, Future}
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait SimpleStoreTest[Id, Key, Data, TxStatus, Isolation, Consistency] {

	def assertUpdate(id : Id, key : Key, data : Data, txid : Option[Id], deps : (Id, Key)*)(actual : Option[Update[Id, Key, Data]]): Unit = {
		assertEquals(Some(Update(id, key, data, txid, deps : _*)), actual)
	}

}

object SimpleStoreTest {
	abstract class Single[Data : TypeTag] extends SimpleStoreTest[Integer, String, Data, String, String, String] {

		type Id = Integer
		type Key = String
		type TxStatus = String
		type Isolation = String
		type Consistency = String

		//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
		protected var store : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]]  = null

		@Before
		def setup(): Unit = {
			store = Stores.Simple.newTestStore[Data](LocalCluster, initialize = true)
		}
	}

	abstract class Multi[Data : TypeTag] extends SimpleStoreTest[Integer, String, Data, String, String, String] {

		type Id = Integer
		type Key = String
		type TxStatus = String
		type Isolation = String
		type Consistency = String

		protected var stores : Seq[SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Data]]]  = null

		protected implicit val executionContext : ExecutionContext = ExecutionContext.global

		@Before
		def setup(): Unit = {

			val idOps = Stores.Simple.createSeqIds

			stores = Seq(
				Stores.Simple.newStore[Data](LocalClusterNode1, idOps = idOps, initialize = true),
				Stores.Simple.newStore[Data](LocalClusterNode1, idOps = idOps),
				Stores.Simple.newStore[Data](LocalClusterNode2, idOps = idOps),
				Stores.Simple.newStore[Data](LocalClusterNode3, idOps = idOps)
			)
		}

		protected def resetStores(): Unit = {
			stores.foreach(_.reset())
		}

		protected def parallelSession[U](
      store : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Data]]
    )(
      session : store.Session[U]
    ): Future[U] = {
			val fut = store.parallelSession(session)
			fut
		}

		protected def barrier[U](futures : Future[U]*): Seq[U] = {
			import scala.concurrent.duration._
			val result = Await.result(Future.sequence[U, Seq](futures), Duration.Inf)

			result

//			Log.info(null, s"result = $result")
//
//			futures.foreach(future => future.onComplete {
//				case Success(_) =>
//				case Failure(e) =>
//					throw e
//			})
		}




	}
}
