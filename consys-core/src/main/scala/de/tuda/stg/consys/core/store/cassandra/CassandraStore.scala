package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import com.datastax.oss.driver.api.core.cql.{BatchStatementBuilder, ResultSet, SimpleStatement, Statement}
import com.datastax.oss.driver.api.core.{CqlSession, ConsistencyLevel => CassandraLevel}
import com.datastax.oss.driver.api.querybuilder.QueryBuilder
import com.datastax.oss.driver.api.querybuilder.insert.Insert
import com.datastax.oss.driver.api.querybuilder.select.Selector
import de.tuda.stg.consys.core.store.{ConsistencyLevel, CoordinationMechanism}
import de.tuda.stg.consys.core.store.cassandra.CassandraStore.CassandraStoreId
import de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaAdapter
import de.tuda.stg.consys.core.store.extensions.{ClearableStore, DistributedStore, ETCDStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.extensions.coordination.{BarrierStore, ETCDBarrierStore, ETCDLockingTransactionContext, ZookeeperBarrierStore, ZookeeperLockingTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect
import io.aeron.exceptions.DriverTimeoutException
import io.etcd.jetcd.Client

import java.io._
import java.lang.reflect.Field
import java.net.InetSocketAddress
import java.nio.ByteBuffer
import org.apache.curator.framework.CuratorFramework

import java.util.concurrent.TimeUnit
import scala.concurrent.TimeoutException
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.reflect.ClassTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait CassandraStore extends DistributedStore
	with BarrierStore
	with ClearableStore {

	override final type Id = CassandraStoreId

	override final type Addr = String
	override final type ObjType = java.io.Serializable

	override final type TxContext = CassandraTransactionContext[_ <: CassandraStore]

	override final type HandlerType[T <: ObjType] = CassandraHandler[T]
	override final type RefType[T <: ObjType] = CassandraRef[T]

	override final type Level = CassandraConsistencyLevel

	protected[cassandra] val cassandraSession : CqlSession

	private[cassandra] val cassandra = new CassandraReplicaAdapter(cassandraSession, timeout)
	if (initializing) cassandra.setup()

	/**
	 * This flag states whether the creation should initialize tables etc.
 	 */
	protected def initializing : Boolean

	override def transaction[U](body : TxContext => Option[U]) : Option[U] = this.synchronized {
		val tx = createTransactionContext()
		CassandraStores.currentTransaction.withValue(tx) {
			try {
				body(tx) match {
					case None => None
					case res@Some(_) =>
						tx.commit()
						res
				}
			} finally {
				tx.releaseAllLocks()
			}
		}
	}

	protected def createTransactionContext() : TxContext

	override def close(): Unit = {
		super.close()
		cassandraSession.close()
	}

	override lazy val id : CassandraStoreId = CassandraStoreId(s"cassandra-store@${cassandraSession.getContext.getSessionName}")

	override def clear() : Unit = {
		cassandra.setup()
	}
}

object CassandraStore {

	case class CassandraStoreId(name : String)

	case class AddrNotAvailableException(addr : String) extends Exception(s"address <$addr> not available")

	def fromAddress(host : String, cassandraPort : Int, coordinationMechanism: CoordinationMechanism, datacenter : String = "OSS-dc0", timeout : FiniteDuration = Duration(30, TimeUnit.SECONDS), initialize : Boolean = false) : CassandraStore = {
		val cassandraSession = CqlSession.builder()
			.addContactPoint(InetSocketAddress.createUnresolved(host, cassandraPort))
			.withLocalDatacenter(datacenter)
			.build()

		coordinationMechanism match {
			case CoordinationMechanism.Zookeeper(zookeeperPort) =>
				val curator = ZookeeperStore.createCurator(host, zookeeperPort)

				class CassandraStoreImpl(
					override val cassandraSession : CqlSession,
					override val curator : CuratorFramework,
					override val timeout : FiniteDuration,
					override val initializing : Boolean)
				extends CassandraStore with ZookeeperStore with ZookeeperBarrierStore {
					def createTransactionContext() =
						new CassandraTransactionContext[CassandraStoreImpl](this) with ZookeeperLockingTransactionContext[CassandraStoreImpl]

					override def close(): Unit = {
						curator.close()
						super.close()
					}
				}

				new CassandraStoreImpl(
					cassandraSession,
					curator,
					timeout = timeout,
					initializing = initialize
				)

			case CoordinationMechanism.ETCD(etcdPort) =>
				val (client, lease) = ETCDStore.createClientAndLease(host, etcdPort, timeout)

				class CassandraStoreImpl(
					override val cassandraSession : CqlSession,
					override val etcdClient : Client,
					override val etcdLease : Long,
					override val timeout : FiniteDuration,
					override val initializing : Boolean)
				extends CassandraStore with ETCDStore with ETCDBarrierStore {
					def createTransactionContext() =
						new CassandraTransactionContext[CassandraStoreImpl](this) with ETCDLockingTransactionContext[CassandraStoreImpl]

					override def close(): Unit = {
						client.getLeaseClient.revoke(lease)
						super.close()
					}
				}

				new CassandraStoreImpl(
					cassandraSession,
					client,
					lease,
					timeout = timeout,
					initializing = initialize
				)
		}
	}
}
