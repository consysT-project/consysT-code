package de.tuda.consys.formalization.backend

import com.datastax.oss.driver.api.core.CqlSession
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.cassandra.CassandraStore.CassandraStoreId
import de.tuda.stg.consys.core.store.extensions.{ClearableStore, DistributedStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.extensions.coordination.ZookeeperBarrierStore
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry

import java.net.InetSocketAddress
import java.util.concurrent.TimeUnit
import scala.concurrent.duration.{Duration, FiniteDuration}

trait Store extends DistributedStore
    with ZookeeperStore
    with ZookeeperBarrierStore
    with ClearableStore {

    override final type Id = CassandraStoreId

    override final type Addr = String
    override final type ObjType = Serializable

    override final type TxContext = FormalizationTransactionContext

    val cassandraSession: CqlSession

    val cassandra = new CassandraReplicaAdapter(cassandraSession, timeout)
    if (initializing) cassandra.setup()

    protected def initializing : Boolean

    private var currentTransaction: Option[FormalizationTransactionContext] = None

    def getCurrentTransaction: Option[FormalizationTransactionContext] = currentTransaction

    def startTransaction()(implicit ct: ClassTable): Unit = {
        currentTransaction = Some(new FormalizationTransactionContext(this))
    }

    def closeTransaction(): Unit = {
        try {
            currentTransaction.get.commit()
        } finally {
            currentTransaction.get.releaseAllLocks()
        }
    }

    override def transaction[T](body: FormalizationTransactionContext => Option[T]): Option[T] =
        throw new NotImplementedError("Use the other transaction method")

    override def close(): Unit = {
        super.close()
        curator.close()
        cassandraSession.close()
    }

    override def id: CassandraStoreId = CassandraStoreId(s"cassandra-store@${cassandraSession.getContext.getSessionName}")

    override def clear(): Unit = {
        cassandra.setup()
    }
}

object Store{
    case class StoreId(name: String)

    case class AddrNotAvailableException(addr: String) extends Exception(s"address <$addr> not available")

    def fromAddress(host: String, cassandraPort: Int, zookeeperPort: Int, datacenter: String = "OSS-dc0",
                    timeout: FiniteDuration = Duration(30, TimeUnit.SECONDS),
                    initialize: Boolean = false): Store = {

        class StoreImpl(override val cassandraSession: CqlSession,
                        override val curator: CuratorFramework,
                        override val timeout: FiniteDuration,
                        override val initializing: Boolean
                       ) extends Store

        val cassandraSession = CqlSession.builder()
            .addContactPoint(InetSocketAddress.createUnresolved(host, cassandraPort))
            .withLocalDatacenter(datacenter)
            .build()

        val curator = CuratorFrameworkFactory
            .newClient(s"$host:$zookeeperPort", new ExponentialBackoffRetry(250, 3))

        curator.start()
        curator.blockUntilConnected()

        new StoreImpl(
            cassandraSession,
            curator,
            timeout = timeout,
            initializing = initialize
        )
    }
}
