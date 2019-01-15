package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import java.nio.ByteBuffer
import java.util.UUID
import java.util.concurrent.atomic.AtomicInteger

import com.datastax.driver.core.utils.UUIDs
import com.datastax.driver.core.{Cluster, TypeCodec}
import de.tudarmstadt.consistency.storelayer.distribution._

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraBinding[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	extends CassandraSessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	with IdService[Id]
	with TxidService[Txid]
	with CassandraDatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	with CassandraCoordinationService[Txid, TxStatus, Isolation]
	with CassandraOptimisticLocksService[Id, Txid, Key]
	with TxStatusBindings[TxStatus]
	with IsolationBindings[Isolation]
	with ConsistencyBindings[Consistency] {

	val connectionParams: ConnectionParams

	override val cluster : Cluster = connectionParams.connectCluster
	override val session : CassandraSession = cluster.connect()

	override def initialize(reset : Boolean = false): Unit = {
		if (reset) {
			CREATE_KEYSPACE()
			USE_KEYSPACE()
			CREATE_CAS_TX_TABLE()
			CREATE_DATA_TABLE()
			CREATE_LOCK_TABLE()
		} else {
			USE_KEYSPACE()
		}
	}

}

object CassandraBinding {

	class DefaultCassandraStore(val connectionParams: ConnectionParams = ConnectionParams.LocalCluster) extends CassandraBinding[UUID, UUID, String, ByteBuffer, Int, Int, Int] {

		object TxStatusOpsImpl extends TxStatusOps {
			override def ABORTED : Int = -1
			override def COMMITTED : Int = 1
			override def PENDING : Int = 0
		}
		override val TxStatus : TxStatusOps = TxStatusOpsImpl

		object IsolationOpsImpl extends IsolationOps {
			override def SI : Int = 4
			override def RC : Int = 2
			override def RU : Int = 1
			override def NONE : Int = 0
		}
		override val Isolation : IsolationOps = IsolationOpsImpl

		object ConsistencyOpsImpl extends ConsistencyOps {
			override def INCONSISTENT : Int = 12
			override def CAUSAL : Int = 5
			override def WEAK : Int = 1
			override def LOCAL : Int = 0
		}
		override val Consistency : ConsistencyOps = ConsistencyOpsImpl


		override def freshId() : UUID = UUIDs.timeBased()

		override def freshTxid() : UUID = UUIDs.timeBased()


		override val keyspaceName : String = "k_default"

		override val typeBinding : CassandraTypeBinding[UUID, UUID, String, ByteBuffer, Int, Int, Int] = {
			new CassandraTypeBinding[UUID, UUID, String, ByteBuffer, Int, Int, Int]()(
				TypeCodec.timeUUID(),
				TypeCodec.timeUUID(),
				TypeCodec.varchar(),
				TypeCodec.blob(),
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]]
			)
		}
	}



	class SimpleCassandraStore(val connectionParams: ConnectionParams = ConnectionParams.LocalCluster) extends CassandraBinding[Int, Int, String, Double, String, String, String] {

		object TxStatusOpsImpl extends TxStatusOps {
			override def ABORTED : String = "abort"
			override def COMMITTED : String = "commit"
			override def PENDING : String = "pending"
		}
		override val TxStatus : TxStatusOps = TxStatusOpsImpl

		object IsolationOpsImpl extends IsolationOps {
			override def SI : String = "SI"
			override def RC : String = "RC"
			override def RU : String = "RU"
			override def NONE : String = "XX"
		}
		override val Isolation : IsolationOps = IsolationOpsImpl

		object ConsistencyOpsImpl extends ConsistencyOps {
			override def INCONSISTENT : String = "INCONST"
			override def CAUSAL : String = "CAUSAL"
			override def WEAK : String = "WEAK"
			override def LOCAL : String = "LOCAL"
		}
		override val Consistency : ConsistencyOps = ConsistencyOpsImpl

		private var currentId : AtomicInteger = new AtomicInteger(0)
		private var currentTxid : AtomicInteger = new AtomicInteger(0)

		override def freshId() : Int = currentId.incrementAndGet()
		override def freshTxid() : Int = currentTxid.addAndGet(1000)


		override val keyspaceName : String = "k_simple"

		override val typeBinding : CassandraTypeBinding[Int, Int, String, Double, String, String, String] = {
			new CassandraTypeBinding[Int, Int, String, Double, String, String, String]()(
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.ascii(),
				TypeCodec.cdouble().asInstanceOf[TypeCodec[Double]],
				TypeCodec.varchar(),
				TypeCodec.varchar(),
				TypeCodec.varchar()
			)
		}
	}

}