package de.tuda.stg.consys.core.store.akka

import akka.actor.{ActorSystem, ExtendedActorSystem}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.AkkaAddress
import de.tuda.stg.consys.core.store.extensions.store.DistributedStore
import de.tuda.stg.consys.utils.Logger

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.FiniteDuration

class AkkaStore(val system : ActorSystem) extends DistributedStore {


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
  override def id: Id = system.name

  override val timeout: FiniteDuration = FiniteDuration.apply(30, TimeUnit.SECONDS)

  private[akka] val replica : BackendReplica = new BackendReplica(system, timeout)


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
      case e =>
        Logger.err("transaction failed executing")
        e.printStackTrace(Logger.err)
        None
    }

  }

  def getAddress : AkkaAddress =
    AkkaUtils.getActorSystemAddress(system)
}

object AkkaStore {

  final val DEFAULT_ACTOR_SYSTEM_NAME : String = "consys-actors"
  final val DEFAULT_ACTOR_NAME = "consys-replica"


  def fromAddress(hostname : String, port : Int) : AkkaStore = {
    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(hostname))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(port))
      .resolve()

    //Creates the actor system
    val system = akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, config)
    Logger.info(s"created actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    new AkkaStore(system)
  }

}
