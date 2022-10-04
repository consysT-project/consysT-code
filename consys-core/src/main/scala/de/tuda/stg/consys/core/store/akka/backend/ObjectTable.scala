package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.typed.{ActorRef, Behavior}
import akka.actor.typed.scaladsl.Behaviors
import akka.cluster.ddata.typed.scaladsl.{DistributedData, Replicator}
import akka.cluster.ddata.{GCounter, GCounterKey, SelfUniqueAddress}

object ObjectTable {


  sealed trait Command
  case object Increment extends Command
  final case class GetValue(replyTo: ActorRef[Int]) extends Command
  final case class GetCachedValue(replyTo: ActorRef[Int]) extends Command
  case object Unsubscribe extends Command


  private sealed trait InternalCommand extends Command
  private case class InternalUpdateResponse(rsp: Replicator.UpdateResponse[GCounter]) extends InternalCommand
  private case class InternalGetResponse(rsp: Replicator.GetResponse[GCounter], replyTo: ActorRef[Int])
      extends InternalCommand
  private case class InternalSubscribeResponse(chg: Replicator.SubscribeResponse[GCounter]) extends InternalCommand




  def apply(key: GCounterKey): Behavior[Command] =
    Behaviors.setup[Command] { context =>
      implicit val node: SelfUniqueAddress = DistributedData(context.system).selfUniqueAddress

      // adapter that turns the response messages from the replicator into our own protocol
      DistributedData.withReplicatorMessageAdapter[Command, GCounter] { replicatorAdapter =>
        // Subscribe to changes of the given `key`.
        replicatorAdapter.subscribe(key, InternalSubscribeResponse.apply)

        def updated(cachedValue: Int): Behavior[Command] = {
          Behaviors.receiveMessage[Command] {
            case Increment =>
              replicatorAdapter.askUpdate(
                askReplyTo => Replicator.Update(key, GCounter.empty, Replicator.WriteLocal, askReplyTo)(_ :+ 1),
                InternalUpdateResponse.apply)

              Behaviors.same

            case GetValue(replyTo) =>
              replicatorAdapter.askGet(
                askReplyTo => Replicator.Get(key, Replicator.ReadLocal, askReplyTo),
                value => InternalGetResponse(value, replyTo))

              Behaviors.same

            case GetCachedValue(replyTo) =>
              replyTo ! cachedValue
              Behaviors.same

            case Unsubscribe =>
              replicatorAdapter.unsubscribe(key)
              Behaviors.same

            case internal: InternalCommand =>
              internal match {
                case InternalUpdateResponse(_) => Behaviors.same // ok

                case InternalGetResponse(rsp @ Replicator.GetSuccess(`key`), replyTo) =>
                  val value = rsp.get(key).value.toInt
                  replyTo ! value
                  Behaviors.same

                case InternalGetResponse(_, _) =>
                  Behaviors.unhandled // not dealing with failures
                case InternalSubscribeResponse(chg @ Replicator.Changed(`key`)) =>
                  val value = chg.get(key).value.intValue
                  updated(value)

                case InternalSubscribeResponse(Replicator.Deleted(_)) =>
                  Behaviors.unhandled // no deletes

                case InternalSubscribeResponse(_) => // changed but wrong key
                  Behaviors.unhandled

              }
          }
        }

        updated(cachedValue = 0)
      }
    }
}