package de.tuda.stg.consys.core.store.akkacluster

import akka.actor.{ActorSystem, ExtendedActorSystem}
import akka.cluster.Cluster
import akka.cluster.ddata.SelfUniqueAddress
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.AkkaAddress
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter
import de.tuda.stg.consys.core.store.extensions.coordination.ZookeeperBarrierStore
import de.tuda.stg.consys.core.store.extensions.{ClearableStore, DistributedStore, ZookeeperStore}
import de.tuda.stg.consys.logging.Logger
import org.apache.curator.framework.CuratorFramework

import scala.concurrent.{Await, Future}

trait AkkaClusterStore extends DistributedStore
  with ZookeeperStore
  with ZookeeperBarrierStore
  with ClearableStore {

  /** The actor system to use for this store. */
  def actorSystem : ExtendedActorSystem
  /** The zookeeper curator to use for all zookeeper calls in this store. */
  def curator : CuratorFramework

  /** Type for ids to identify different replicas of the store. */
  override type Id = SelfUniqueAddress

  /** Type for addresses of objects in the store. */
  override type Addr = String

  /** Supertype for all objects that can be stored in the store. */
  override type ObjType = java.io.Serializable

  /** Type of transactions contexts in the store that defines what users can do with transactions. */
  override type TxContext = AkkaClusterTransactionContext

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
  private[akkacluster] val replica : AkkaClusterReplicaAdapter = new AkkaClusterReplicaAdapter(actorSystem, curator, timeout)


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
    val tx = new AkkaClusterTransactionContext(this)

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
    curator.close()
    replica.close()
    Await.ready(actorSystem.whenTerminated, timeout)
  }

  override def clear() : Unit = {
//    replica.clear()
    ???
  }

}


