package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.typed.{ActorRef, Behavior}
import akka.actor.typed.scaladsl.Behaviors
import akka.cluster.ddata.typed.scaladsl.Replicator.{Command, GetSuccess}
import akka.cluster.ddata.typed.scaladsl.{DistributedData, Replicator}
import akka.cluster.ddata.{GCounter, GCounterKey, GSet, LWWRegister, ORMap, ORMapKey, ReplicatedData, SelfUniqueAddress}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.akka.AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME

import java.util.concurrent.CountDownLatch

object AkkaReplicatedDataAdapter {
  private[AkkaReplicatedDataAdapter] type ObjectMap = ORMap[String, ReplicatedData]
  private[AkkaReplicatedDataAdapter]type ObjectMapKey = ORMapKey[String, ReplicatedData]

  private[AkkaReplicatedDataAdapter] val mapKey : ObjectMapKey = ORMapKey[String, ReplicatedData]("object-table")


  private[AkkaReplicatedDataAdapter] case class PutAnyCommand(key : String, obj : Any) extends Command
  private[AkkaReplicatedDataAdapter] case class GetAnyCommand(replyTo : ActorRef[Option[ReplicatedData]], key : String) extends Command

  private[AkkaReplicatedDataAdapter] sealed trait InternalCommand extends Command
  private[AkkaReplicatedDataAdapter] case class InternalUpdateResponse(rsp: Replicator.UpdateResponse[ObjectMap]) extends InternalCommand
  private[AkkaReplicatedDataAdapter] case class InternalGetResponse(rsp: Replicator.GetResponse[ObjectMap], replyTo: ActorRef[Option[ReplicatedData]], key : String)
    extends InternalCommand
  private[AkkaReplicatedDataAdapter] case class InternalSubscribeResponse(chg: Replicator.SubscribeResponse[ObjectMap]) extends InternalCommand


  def main(args : Array[String]) : Unit = {
    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
      .resolve()

    val table = new AkkaReplicatedDataAdapter(akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, config))

    table.put("obj1", Set(1, 2, 42))
    println("get1 = " + table.get("obj1"))
    println("get2 = " + table.get("obj1"))
  }


}

class AkkaReplicatedDataAdapter(system : akka.actor.typed.ActorSystem[_]) {

  def this(_system : akka.actor.ActorSystem) =
    this(akka.actor.typed.ActorSystem.wrap(_system))


  import AkkaReplicatedDataAdapter._


  val behavior = Behaviors.setup[Command] { context =>
    implicit val node: SelfUniqueAddress = DistributedData(context.system).selfUniqueAddress

    // adapter that turns the response messages from the replicator into our own protocol
    DistributedData.withReplicatorMessageAdapter[Command, ObjectMap] { replicatorAdapter =>
      // Subscribe to changes of the given `key`.
      replicatorAdapter.subscribe(mapKey, response => InternalSubscribeResponse(response))

      Behaviors.receiveMessage[Command] {
        case PutAnyCommand(key, obj) =>
          replicatorAdapter.askUpdate(
            askReplyTo => Replicator.Update[ObjectMap](mapKey, ORMap.empty[String, ReplicatedData], Replicator.WriteLocal, askReplyTo)(
              map => map.put(node, key, LWWRegister.create(obj))
            ),
            response => {
              InternalUpdateResponse(response)
            }
          )
          Behaviors.same

        case GetAnyCommand(replyTo, key) =>
          replicatorAdapter.askGet(
            askReplyTo => Replicator.Get(mapKey, Replicator.ReadLocal, askReplyTo),
            response => {
              InternalGetResponse(response, replyTo, key)
            }
          )
          Behaviors.same

        case InternalGetResponse(res@GetSuccess(retrievedKey), replyTo, key) =>
          val objMap = res.get(retrievedKey)
          val result = objMap.get(key)
          replyTo ! result
          Behaviors.same

        case InternalUpdateResponse(res) =>
          Behaviors.same

        //            case GetValue(replyTo) =>
        //              replicatorAdapter.askGet(
        //                askReplyTo => Replicator.Get(objectMapKey, Replicator.ReadLocal, askReplyTo),
        //                value => InternalGetResponse(value, replyTo))
        //
        //              Behaviors.same
        //
        //            case GetCachedValue(replyTo) =>
        //              replyTo ! cachedValue
        //              Behaviors.same
        //
        //            case Unsubscribe =>
        //              replicatorAdapter.unsubscribe(objectMapKey)
        //              Behaviors.same
        //
        //            case internal: InternalCommand =>
        //              internal match {
        //                case InternalUpdateResponse(_) => Behaviors.same // ok
        //
        //                case InternalGetResponse(rsp @ Replicator.GetSuccess(`objectMapKey`), replyTo) =>
        //                  val value = rsp.get(objectMapKey).value.toInt
        //                  replyTo ! value
        //                  Behaviors.same
        //
        //                case InternalGetResponse(_, _) =>
        //                  Behaviors.unhandled // not dealing with failures
        //                case InternalSubscribeResponse(chg @ Replicator.Changed(`objectMapKey`)) =>
        //                  val value = chg.get(objectMapKey).value.intValue
        //                  updated(value)
        //
        //                case InternalSubscribeResponse(Replicator.Deleted(_)) =>
        //                  Behaviors.unhandled // no deletes
        //
        //                case InternalSubscribeResponse(_) => // changed but wrong key
        //                  Behaviors.unhandled
        //
        //              }
      }
    }
  }


   val adapter : ActorRef[Command] = akka.actor.typed.ActorSystem(behavior, "table-adapter")

  def get(addr : String) : Option[Any] = {
    //TODO: Can we do this in a better way?
    var result : Option[ReplicatedData] = null
    val latch = new CountDownLatch(1)

    val getter = Behaviors.receiveMessage[Option[ReplicatedData]] { received =>
        result = received
        latch.countDown()
        Behaviors.stopped
    }

    val replyTo = system.systemActorOf(getter, "get-any-" + System.nanoTime())

    adapter ! GetAnyCommand(replyTo, addr)

    latch.await()

    result match {
      case Some(LWWRegister(value)) =>
        Some(value)
      case None =>
        None
    }

  }

  def put(addr : String, obj : Any) : Unit = {
    adapter ! PutAnyCommand("obj1", obj)
  }








}