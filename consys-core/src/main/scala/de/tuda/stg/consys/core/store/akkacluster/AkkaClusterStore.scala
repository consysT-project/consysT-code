package de.tuda.stg.consys.core.store.akkacluster

import akka.actor.{AllDeadLetters, ExtendedActorSystem, Props}
import akka.cluster.Cluster
import akka.cluster.ddata.SelfUniqueAddress
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, CoordinationMechanism}
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.AkkaAddress
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter
import de.tuda.stg.consys.core.store.extensions.coordination.{BarrierStore, ETCDBarrierStore, ETCDLockingTransactionContext, ZookeeperBarrierStore, ZookeeperLockingTransactionContext}
import de.tuda.stg.consys.core.store.extensions.{ClearableStore, DistributedStore, ETCDStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.utils.{DeadLetterListener, SinglePortAddress}
import de.tuda.stg.consys.logging.Logger
import io.etcd.jetcd.Client
import org.apache.curator.framework.CuratorFramework

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.concurrent.{Await, Future}

trait AkkaClusterStore extends DistributedStore
  with BarrierStore
  with ClearableStore {

  /** The actor system to use for this store. */
  def actorSystem : ExtendedActorSystem

  /** Type for ids to identify different replicas of the store. */
  override type Id = SelfUniqueAddress

  /** Type for addresses of objects in the store. */
  override type Addr = String

  /** Supertype for all objects that can be stored in the store. */
  override type ObjType = java.io.Serializable

  /** Type of transactions contexts in the store that defines what users can do with transactions. */
  override type TxContext = AkkaClusterTransactionContext[_ <: AkkaClusterStore]

  /** The type of handlers of stored object that handle, e.g., method calls. */
  override type HandlerType[T <: ObjType] = AkkaClusterHandler[T]
  /** The type of references to stored objects. */
  override type RefType[T <: ObjType] = AkkaClusterRef[T]

  /** The type of levels that are useable in this store. */
  override type Level = ConsistencyLevel[AkkaClusterStore]

  /** Returns an identifier of this replica of the store. It has to be
   * unique for each replica. */
  override lazy val id : Id = SelfUniqueAddress(Cluster(actorSystem).selfUniqueAddress)

  /** The backend replica implementation. */
  private[akkacluster] val replica : AkkaClusterReplicaAdapter = new AkkaClusterReplicaAdapter(actorSystem, timeout)


  /**
   * Executes a new transaction on the store. Transactions are expected
   * to be short lived.
   *
   * @param body The code that is executed in the transaction.
   * @tparam T The result type of the transaction.
   * @return The result of the transaction or [[None]] if the transaction does
   *         not produce a result or has been aborted by the system.
   */
  override def transaction[T](body: TxContext => Option[T]): Option[T] = {
    val tx = createTransactionContext()

    AkkaClusterStores.currentTransaction.withValue(tx) {
      try {
        body(tx) match {
          case None => None
          case res@Some(_) =>
            tx.commit()
            res
        }
      } catch {
        case e : Exception =>
          Logger.err("transaction failed executing")
          e.printStackTrace(Logger.err)
          None
      } finally {
        // Always release the locks after the trnasaction is done.
        tx.releaseAllLocks()
      }
    }
  }

  protected def createTransactionContext() : TxContext

  def getAddress : AkkaAddress =
    replica.getAddress

  def addOtherReplica(hostname : String, port : Int) : Unit = {
//    replica.addOtherReplica(hostname, port)
    ???
  }

  def addOtherReplicaAsync(hostname : String, port : Int) : Future[Unit] = {
//    replica.addOtherReplicaAsync(hostname, port)
    ???
  }

  override def close() : Unit = {
    replica.close()
    Await.ready(actorSystem.whenTerminated, timeout)
  }

  override def clear() : Unit = {
//    replica.clear()
    ???
  }

}


object AkkaClusterStore {


  def fromAddress(host : String, akkaPort : Int, coordinationMechanism : CoordinationMechanism, nodes : Iterable[SinglePortAddress], systemName : String = "consys-akka-cluster", timeout : FiniteDuration = Duration(30, TimeUnit.SECONDS)) : AkkaClusterStore = {
    def nodeName(host : String, akkaPort : Int) : String =
      s"akka://$systemName@$host:$akkaPort"

    val nodeNames : Iterable[String] = nodes.map(address => nodeName(address.hostname, address.port))

    import scala.jdk.CollectionConverters._

    val config = ConfigFactory.load("akkacluster.conf")
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(host))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(akkaPort))
      .withValue("akka.cluster.seed-nodes", ConfigValueFactory.fromIterable(nodeNames.asJava))
      .resolve()

    //Creates the actor system
    val system = akka.actor.ActorSystem(systemName, config).asInstanceOf[ExtendedActorSystem]
    Logger.info(s"started actor system at ${system.provider.getDefaultAddress}")

    DeadLetterListener.addDeadLetterListener(system)

    coordinationMechanism match {
      case CoordinationMechanism.Zookeeper(zookeeperPort) =>
        val curator = ZookeeperStore.createCurator(host, zookeeperPort)

        class AkkaClusterStoreImpl(
          override val actorSystem : ExtendedActorSystem,
          override val curator : CuratorFramework,
          override val timeout : FiniteDuration)
        extends AkkaClusterStore with ZookeeperStore with ZookeeperBarrierStore {
          def createTransactionContext() =
            new AkkaClusterTransactionContext[AkkaClusterStoreImpl](this) with ZookeeperLockingTransactionContext[AkkaClusterStoreImpl]

          override def close(): Unit = {
            curator.close()
            super.close()
          }
        }

        new AkkaClusterStoreImpl(system, curator, timeout)

      case CoordinationMechanism.ETCD(etcdPort) =>
        val (client, lease) = ETCDStore.createClientAndLease(host, etcdPort, timeout)

        class AkkaClusterStoreImpl(
          override val actorSystem : ExtendedActorSystem,
          override val etcdClient : Client,
          override val etcdLease : Long,
          override val timeout : FiniteDuration)
        extends AkkaClusterStore with ETCDStore with ETCDBarrierStore {
          def createTransactionContext() =
            new AkkaClusterTransactionContext[AkkaClusterStoreImpl](this) with ETCDLockingTransactionContext[AkkaClusterStoreImpl]

          override def close(): Unit = {
            client.getLeaseClient.revoke(lease)
            super.close()
          }
        }

        new AkkaClusterStoreImpl(system, client, lease, timeout)
    }
  }
}


