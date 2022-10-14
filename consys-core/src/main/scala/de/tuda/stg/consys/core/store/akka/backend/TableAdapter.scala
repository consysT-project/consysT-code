package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.typed.{ActorRef, Behavior}
import akka.actor.typed.scaladsl.Behaviors
import akka.cluster.ddata.typed.scaladsl.Replicator.{Command, GetSuccess}
import akka.cluster.ddata.typed.scaladsl.{DistributedData, Replicator}
import akka.cluster.ddata.{GCounter, GCounterKey, GSet, LWWRegister, ORMap, ORMapKey, ReplicatedData, SelfUniqueAddress}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.akka.AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME

object TableAdapter {

  type ObjectMap = ORMap[String, ReplicatedData]
  type ObjectMapKey = ORMapKey[String, ReplicatedData]

  val mapKey : ObjectMapKey = ORMapKey[String, ReplicatedData]("object-table")



  case class PutAnyCommand(key : String, obj : Any) extends Command
  case class GetAnyCommand(replyTo : ActorRef[Option[ReplicatedData]], key : String) extends Command

  sealed trait InternalCommand extends Command
  private case class InternalUpdateResponse(rsp: Replicator.UpdateResponse[ObjectMap]) extends InternalCommand
  private case class InternalGetResponse(rsp: Replicator.GetResponse[ObjectMap], replyTo: ActorRef[Option[ReplicatedData]], key : String)
    extends InternalCommand
  private case class InternalSubscribeResponse(chg: Replicator.SubscribeResponse[ObjectMap]) extends InternalCommand

  def main(args : Array[String]) : Unit = {
    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
      .resolve()

    //Creates the actor system
    val system = akka.actor.typed.ActorSystem.wrap(akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, config))

    implicit val node: SelfUniqueAddress = DistributedData(system).selfUniqueAddress

    val printer = Behaviors.receiveMessage[Any] {
      x =>
        println("recevied: " + x)
        Behaviors.same
    }

    val printerActor = system.systemActorOf(printer, "printer")


    val actor = system.systemActorOf(TableAdapter.apply(), "object-table-actor")
    actor ! PutAnyCommand("obj1", new String())
    actor ! GetAnyCommand(printerActor, "obj1")
  }


  def apply(): Behavior[Command] = {

    Behaviors.setup[Command] { context =>
      implicit val node: SelfUniqueAddress = DistributedData(context.system).selfUniqueAddress

      // adapter that turns the response messages from the replicator into our own protocol
      DistributedData.withReplicatorMessageAdapter[Command, ObjectMap] { replicatorAdapter =>
        // Subscribe to changes of the given `key`.
        replicatorAdapter.subscribe(mapKey, response => InternalSubscribeResponse(response))

        Behaviors.receiveMessage[Command] {
          case PutAnyCommand(key, obj) =>
            println("put any command")
            replicatorAdapter.askUpdate(
              askReplyTo => Replicator.Update[ObjectMap](mapKey, ORMap.empty[String, ReplicatedData], Replicator.WriteLocal, askReplyTo)(
                map => map.put(node, key, LWWRegister.create(obj))
              ),
              response => {
                println("hallllllo")
                InternalUpdateResponse(response)
              }
            )

            Behaviors.same

          case GetAnyCommand(replyTo, key) =>
            println("get any command")

            replicatorAdapter.askGet(
              askReplyTo => Replicator.Get(mapKey, Replicator.ReadLocal, askReplyTo),
              response => {
                println("helllo")
                InternalGetResponse(response, replyTo, key)
              }
            )

            Behaviors.same

          case InternalGetResponse(res@GetSuccess(retrievedKey), replyTo, key) =>
            println("internal get")
            val objMap = res.get(retrievedKey)
            val result = objMap.get(key)
            replyTo ! result
            Behaviors.same

          case InternalUpdateResponse(res) =>
            println("internal update")
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
  }


}