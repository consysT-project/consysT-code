package de.tuda.stg.consys.core.store.akka

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, CoordinationMechanism}
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.AkkaAddress
import de.tuda.stg.consys.core.store.extensions.{ClearableStore, DistributedStore, ETCDStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.extensions.coordination.{BarrierStore, ETCDBarrierStore, ETCDLockingTransactionContext, ZookeeperBarrierStore, ZookeeperLockingTransactionContext}
import de.tuda.stg.consys.logging.Logger
import io.etcd.jetcd.Client
import org.apache.curator.framework.CuratorFramework

import java.util.concurrent.TimeUnit
import scala.concurrent.{Await, Future}
import scala.concurrent.duration.{Duration, FiniteDuration}

trait AkkaStore extends DistributedStore
  with BarrierStore
  with ClearableStore {

  /** The actor system to use for this store. */
  def actorSystem : ActorSystem

  /** Type for ids to identify different replicas of the store. */
  override type Id = String

  /** Type for addresses of objects in the store. */
  override type Addr = String

  /** Supertype for all objects that can be stored in the store. */
  override type ObjType = java.io.Serializable

  /** Type of transactions contexts in the store that defines what users can do with transactions. */
  override type TxContext = AkkaTransactionContext[_ <: AkkaStore]

  /** The type of handlers of stored object that handle, e.g., method calls. */
  override type HandlerType[T <: ObjType] = AkkaHandler[T]
  /** The type of references to stored objects. */
  override type RefType[T <: ObjType] = AkkaRef[T]

  /** The type of levels that are useable in this store. */
  override type Level = ConsistencyLevel[AkkaStore]

  /** Returns an identifier of this replica of the store. It has to be
   * unique for each replica. */
  override lazy val id : Id = s"${actorSystem.name}[$getAddress]"

  /** The backend replica implementation. */
  private[akka] val replica : AkkaReplicaAdapter = new AkkaReplicaAdapter(actorSystem, timeout)


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

    AkkaStores.currentTransaction.withValue(tx) {
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

  protected def createTransactionContext(): TxContext

  def getAddress : AkkaAddress =
    AkkaUtils.getActorSystemAddress(actorSystem)

  def addOtherReplica(hostname : String, port : Int) : Unit = {
    replica.addOtherReplica(hostname, port)
  }

  def addOtherReplicaAsync(hostname : String, port : Int) : Future[Unit] = {
    replica.addOtherReplicaAsync(hostname, port)
  }

  override def close() : Unit = {
    replica.close()
    Await.ready(actorSystem.whenTerminated, timeout)
  }

  override def clear() : Unit = {
    replica.clear()
  }

}

object AkkaStore {

  final val DEFAULT_ACTOR_SYSTEM_NAME : String = "consys-actors"
  final val DEFAULT_ACTOR_NAME = "consys-replica"


  def fromAddress(host : String, akkaPort : Int, coordinationMechanism : CoordinationMechanism, timeout : FiniteDuration = Duration(30, TimeUnit.SECONDS)) : AkkaStore = {
    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(host))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(akkaPort))
      .resolve()

    //Creates the actor system
    val system = akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, config)
    Logger.info(s"started actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    coordinationMechanism match {
      case CoordinationMechanism.Zookeeper(zookeeperPort) =>
        val curator = ZookeeperStore.createCurator(host, zookeeperPort)

        class AkkaStoreImpl(
          override val actorSystem : ActorSystem,
          override val curator : CuratorFramework,
          override val timeout : FiniteDuration)
        extends AkkaStore with ZookeeperStore with ZookeeperBarrierStore {
          def createTransactionContext() =
            new AkkaTransactionContext[AkkaStoreImpl](this) with ZookeeperLockingTransactionContext[AkkaStoreImpl]

          override def close(): Unit = {
            curator.close()
            super.close()
          }
        }

        new AkkaStoreImpl(system, curator, timeout)

      case CoordinationMechanism.ETCD(etcdPort) =>
        val (client, lease) = ETCDStore.createClientAndLease(host, etcdPort, timeout)

        class AkkaStoreImpl(
          override val actorSystem : ActorSystem,
          override val etcdClient : Client,
          override val etcdLease : Long,
          override val timeout : FiniteDuration)
        extends AkkaStore with ETCDStore with ETCDBarrierStore {
          def createTransactionContext() =
            new AkkaTransactionContext[AkkaStoreImpl](this) with ETCDLockingTransactionContext[AkkaStoreImpl]

          override def close(): Unit = {
            client.getLeaseClient.revoke(lease)
            super.close()
          }
        }

        new AkkaStoreImpl(system, client, lease, timeout)
    }
  }
}
