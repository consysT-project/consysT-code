package de.tudarmstadt.consistency.storelayer.local

import java.nio.ByteBuffer
import java.util.UUID

import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.distribution.cassandra.CassandraBinding.DefaultCassandraStore
import de.tudarmstadt.consistency.storelayer.distribution.cassandra.ConnectionParams
import de.tudarmstadt.consistency.storelayer.local.LocalLayer.SnapshotIsolatedTransactionsLayer
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol
import org.junit.Test

/**
	* Created on 15.01.19.
	*
	* @author Mirko Köhler
	*/
class CassandraBindingsTest {

	@Test
	def test(): Unit = {
		val cassandraStore : DefaultCassandraStore = new DefaultCassandraStore(ConnectionParams.LocalCluster)
		cassandraStore.initialize(true)

		trait CassandraLayer
			extends LocalLayer[UUID, UUID, String, ByteBuffer, Int, Int, Int]
			with SnapshotIsolatedTransactionsLayer[UUID, UUID, String, ByteBuffer, Int, Int, Int]

		val layer : CassandraLayer = new CassandraLayer {
			override protected val store : SessionService[UUID, UUID, String, ByteBuffer, Int, Int, Int]
				with IdService[UUID]
				with TxidService[UUID]
				with DatastoreService[UUID, UUID, String, ByteBuffer, Int, Int, Int]
				with CoordinationService[UUID, Int, Int]
				with OptimisticLockService[UUID, UUID, String]
				with TxStatusBindings[Int]
				with ConsistencyBindings[Int]
				with IsolationBindings[Int] =
					cassandraStore

		}

		import cassandraStore._
		import layer._

		transaction(Isolation.SI) {
			write(Consistency.CAUSAL, "x", ByteBuffer.wrap(Array(3)))
		}
	}

}
