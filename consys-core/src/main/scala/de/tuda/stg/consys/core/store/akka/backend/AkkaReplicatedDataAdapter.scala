package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.typed.scaladsl.Behaviors
import akka.actor.typed.{ActorRef, ActorSystem}
import akka.cluster.ClusterEvent.{MemberEvent, MemberRemoved, MemberUp, ReachabilityEvent, ReachableMember, UnreachableMember}
import akka.cluster.ddata.typed.scaladsl.Replicator.{Command, GetSuccess}
import akka.cluster.ddata.typed.scaladsl.{DistributedData, Replicator}
import akka.cluster.ddata._
import akka.cluster.typed.{Cluster, Join}
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.akka.AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME

import java.util.concurrent.{CountDownLatch, TimeUnit}
import scala.concurrent.TimeoutException
import scala.concurrent.duration.{Duration, FiniteDuration}
import akka.cluster.typed.Subscribe

import scala.jdk.CollectionConverters._

object AkkaReplicatedDataAdapter {
  type ObjectMap = ORMap[String, ReplicatedData]
  type ObjectMapKey = ORMapKey[String, ReplicatedData]

  val mapKey : ObjectMapKey = ORMapKey[String, ReplicatedData]("object-table")

  type Addr = String
  type ObjType = Serializable

  sealed trait TransactionOp
  case class CreateOrUpdateObject(addr : Addr, newState : ObjType) extends TransactionOp


  case class AsyncWriteOps(timestamp : Long, ops : Seq[TransactionOp]) extends Command
  case class SyncWriteOps(await : LatchAwait, timestamp : Long, ops : Seq[TransactionOp]) extends Command
  case class RetrieveValue(await : LatchAwait, reply : RetrievedValue, key : String) extends Command


  sealed trait InternalCommand extends Command
  case object InternalAck extends InternalCommand

  class RetrievedValue {
    var result : Option[ReplicatedData] = null
  }

  class LatchAwait {
    private val latch = new CountDownLatch(1)

    def await(timeout : FiniteDuration) : Unit = {
      val completed = latch.await(timeout.toMillis, TimeUnit.MILLISECONDS)
      if (!completed)
        throw new TimeoutException()
    }

    def complete() : Unit = {
      latch.countDown()
    }
  }


  def main(args : Array[String]) : Unit = {


    val index = Integer.parseInt(args(0))


    val configs = Array(
      ConfigFactory.load()
        .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
        .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
        .withValue("akka.cluster.seed-nodes", ConfigValueFactory.fromIterable(Iterable("akka://consys-actors@127.0.0.1:4445", "akka://consys-actors@127.0.0.2:4446").asJava))
        .resolve(),
      ConfigFactory.load()
        .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.2"))
        .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4446))
        .withValue("akka.cluster.seed-nodes", ConfigValueFactory.fromIterable(Iterable("akka://consys-actors@127.0.0.1:4445", "akka://consys-actors@127.0.0.2:4446").asJava))
        .resolve()
    )


    val actorSystem1 = ActorSystem.wrap(akka.actor.ActorSystem(DEFAULT_ACTOR_SYSTEM_NAME, configs(index)))
    val cluster = Cluster(actorSystem1)

    val subscribeBehavior = Behaviors.receiveMessage[MemberEvent] {
      case MemberUp(member) =>
        println("Member is Up: {}", member.address)
        Behaviors.same
      case MemberRemoved(member, previousStatus) =>
        println("Member is Removed: {} after {}",
          member.address, previousStatus)
        Behaviors.same
      case _ : MemberEvent =>
        // ignore
        Behaviors.same
    }

    val reachableBehavior = Behaviors.receiveMessage[ReachabilityEvent] {
      case UnreachableMember(member) =>
        println("Member detected as unreachable: {}", member)
        Behaviors.same
      case ReachableMember(member) =>
        println("Member back to reachable: {}", member)
        Behaviors.same
    }

    cluster.subscriptions ! Subscribe(actorSystem1.systemActorOf(subscribeBehavior, "cluster-members"), classOf[MemberEvent])
    cluster.subscriptions ! Subscribe(actorSystem1.systemActorOf(reachableBehavior, "cluster-reachable"), classOf[ReachabilityEvent])


    Thread.sleep(10000)

    val table1 = new AkkaReplicatedDataAdapter(actorSystem1, Duration(10, "s"))

    if (index == 0) table1.writeSync(System.currentTimeMillis(), Seq(CreateOrUpdateObject("obj1", Set(1, 2, 42).asInstanceOf[Serializable])))
    println(index + " get = " + table1.read("obj1"))
  }


}

class AkkaReplicatedDataAdapter(val system : ActorSystem[_], val timeout : FiniteDuration) {

  def this(_system : akka.actor.ActorSystem, _timeout : FiniteDuration) =
    this(ActorSystem.wrap(_system), _timeout)


  import AkkaReplicatedDataAdapter._

  private val dd = DistributedData(system)

  private val adapterBehavior = Behaviors.setup[Command] { context =>
    implicit val node: SelfUniqueAddress = dd.selfUniqueAddress

    // adapter that turns the response messages from the replicator into our own protocol
    DistributedData.withReplicatorMessageAdapter[Command, ObjectMap] { replicatorAdapter =>
      // Subscribe to changes of the given `key`.
      replicatorAdapter.subscribe(mapKey, response => InternalAck)

      Behaviors.receiveMessage[Command] {
        case AsyncWriteOps(timestamp, ops) =>
          replicatorAdapter.askUpdate(
            askReplyTo => Replicator.Update[ObjectMap](mapKey, ORMap.empty[String, ReplicatedData], Replicator.WriteLocal, askReplyTo)(
              map =>
                ops.foldLeft(map)((oldMap, op) => {
                  op match {
                    case CreateOrUpdateObject(addr, state) =>
                      oldMap.put(node, addr, LWWRegister.create(state)(node, (currentTimestamp : Long, value : Any) => timestamp))
                  }
                })
            ),
            response => InternalAck
          )
          Behaviors.same

        case SyncWriteOps(await, timestamp, ops) =>
          replicatorAdapter.askUpdate(
            askReplyTo => Replicator.Update[ObjectMap](mapKey, ORMap.empty[String, ReplicatedData], Replicator.WriteLocal, askReplyTo)(
              map =>
                ops.foldLeft(map)((oldMap, op) => {
                  op match {
                    case CreateOrUpdateObject(addr, state) =>
                      oldMap.put(node, addr, LWWRegister.create(state)(node, (currentTimestamp : Long, value : Any) => timestamp))
                  }
                })
            ),
            response => {
              await.complete()
              InternalAck
            }
          )
          Behaviors.same



        case RetrieveValue(await, reply, key) =>
          replicatorAdapter.askGet(
            askReplyTo => Replicator.Get(mapKey, Replicator.ReadLocal, askReplyTo),
            response => {
              response match {
                case res@GetSuccess(retrievedKey) =>
                  val objMap = res.get(retrievedKey)
                  val result = objMap.get(key)
                  reply.result = result
                  await.complete()
              }
              InternalAck
            }
          )
          Behaviors.same

        case InternalAck =>
          Behaviors.same
      }
    }
  }

  val adapter : ActorRef[Command] = system.systemActorOf(adapterBehavior, "table-adapter")


  def writeAsync(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
    adapter ! AsyncWriteOps(timestamp, ops)
  }

  def writeSync(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
    val latch = new LatchAwait

    adapter ! SyncWriteOps(latch, timestamp, ops)

    latch.await(timeout)
  }

  def read[T <: ObjType](addr : Addr) : T  = {
    val startTime = System.nanoTime()

    while (true) {
      val timeTaken = System.nanoTime() - startTime

      if (timeTaken > timeout.toNanos) {
        throw new TimeoutException(s"reference $addr was not resolved")
      }

      // Reply object is mutated by the actor to return a value.
      val reply = new RetrievedValue
      val latch = new LatchAwait

      adapter ! RetrieveValue(latch, reply, addr)

      // Wait for the object to be mutated.
      latch.await(timeout)

      reply.result match {
        case Some(LWWRegister(value : T)) =>
          return value
        case None =>
      }

      Thread.sleep(100)
    }

    throw new NotImplementedError()
  }

}