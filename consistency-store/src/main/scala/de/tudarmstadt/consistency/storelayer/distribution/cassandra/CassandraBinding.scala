package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import java.nio.ByteBuffer
import java.util.UUID

import com.datastax.driver.core.utils.UUIDs
import com.datastax.driver.core.{Cluster, TypeCodec}
import de.tudarmstadt.consistency.storelayer.distribution.{ConsistencyBindings, IdService, IsolationBindings, TxStatusBindings}

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraBinding[Id, Key, Data, TxStatus, Isolation, Consistency]
	extends CassandraSessionService[Id, Key, Data, TxStatus, Isolation, Consistency]
	with IdService[Id]
	with CassandraDatastoreService[Id, Key, Data, TxStatus, Isolation, Consistency]
	with CassandraCoordinationService[Id, TxStatus, Isolation]
	with CassandraOptimisticLocksService[Id, Key]
	with TxStatusBindings[TxStatus]
	with IsolationBindings[Isolation]
	with ConsistencyBindings[Consistency]

object CassandraBinding {

	class DefaultCassandraSession(connectionParams: ConnectionParams) extends CassandraBinding[UUID, String, ByteBuffer, Int, Int, Int] {
		override val cluster : Cluster = connectionParams.connectCluster
		override val session : CassandraSession = cluster.connect()

		object TxStatusOpsImpl extends TxStatusOps {
			override def ABORTED : Int = -1
			override def COMMITTED : Int = 1
			override def PENDING : Int = 0
		}
		override def TxStatus : TxStatusOps = TxStatusOpsImpl

		object IsolationOpsImpl extends IsolationOps {
			override def SI : Int = 4
			override def RC : Int = 2
			override def RU : Int = 1
			override def NONE : Int = 0
		}
		override def Isolation : IsolationOps = IsolationOpsImpl

		object ConsistencyOpsImpl extends ConsistencyOps {
			override def INCONSISTENT : Int = 12
			override def CAUSAL : Int = 5
			override def WEAK : Int = 1
			override def LOCAL : Int = 0
		}
		override def Consistency : ConsistencyOps = ConsistencyOpsImpl

		override def freshId() : UUID = UUIDs.timeBased()

		override val keyspaceName : String = "k_default"

		override val typeBinding : CassandraTypeBinding[UUID, String, ByteBuffer, Int, Int, Int] = {
			new CassandraTypeBinding[UUID, String, ByteBuffer, Int, Int, Int]()(
				TypeCodec.timeUUID(),
				TypeCodec.ascii(),
				TypeCodec.blob(),
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]],
				TypeCodec.cint().asInstanceOf[TypeCodec[Int]]
			)
		}

	}

}