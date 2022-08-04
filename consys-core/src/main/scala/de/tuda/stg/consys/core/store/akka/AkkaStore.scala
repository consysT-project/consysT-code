package de.tuda.stg.consys.core.store.akka

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.AkkaAddress
import de.tuda.stg.consys.core.store.extensions.store.DistributedStore
import de.tuda.stg.consys.utils.Logger
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.{Duration, FiniteDuration}

trait AkkaStore extends DistributedStore {


  /** Type for ids to identify different replicas of the store. */
  override type Id = String

  /** Type for addresses of objects in the store. */
  override type Addr = String

  /** Supertype for all objects that can be stored in the store. */
  override type ObjType = java.io.Serializable

  /** Type of transactions contexts in the store that defines what users can do with transactions. */
  override type TxContext = AkkaTransactionContext

  /** The type of handlers of stored object that handle, e.g., method calls. */
  override type HandlerType[T <: ObjType] = AkkaHandler[T]
  /** The type of references to stored objects. */
  override type RefType[T <: ObjType] = AkkaRef[T]

  /** The type of levels that are useable in this store. */
  override type Level = ConsistencyLevel[AkkaStore]

  /** Returns an identifier of this replica of the store. It has to be
   * unique for each replica. */
  override def id: Id = actorSystem.name

  def actorSystem : ActorSystem
  def curator : CuratorFramework

  private[akka] val replica : AkkaReplicaAdapter = new AkkaReplicaAdapter(actorSystem, curator, timeout)


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
    val context = new AkkaTransactionContext(this)
    try {
      val result = body(context)
      context.commit()
      result
    } catch {
      case e : Exception =>
        Logger.err("transaction failed executing")
        e.printStackTrace(Logger.err)
        None
    }
  }

  def getAddress : AkkaAddress =
    AkkaUtils.getActorSystemAddress(actorSystem)
}

object AkkaStore {

  final val DEFAULT_ACTOR_SYSTEM_NAME : String = "consys-actors"
  final val DEFAULT_ACTOR_NAME = "consys-replica"


  def fromAddress(host : String, akkaPort : Int, zookeeperPort : Int, timeout : FiniteDuration = Duration(30, TimeUnit.SECONDS)) : AkkaStore = {

    class AkkaStoreImpl(
      override val actorSystem : ActorSystem,
      override val curator : CuratorFramework,
      override val timeout : FiniteDuration
    ) extends AkkaStore


    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(host))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(akkaPort))
      .resolve()

    //Creates the actor system
    val system = akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, config)
    Logger.info(s"started actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    val curator = CuratorFrameworkFactory
      .newClient(s"$host:$zookeeperPort", new ExponentialBackoffRetry(250, 3))

    new AkkaStoreImpl(system, curator, timeout)

  }

}
