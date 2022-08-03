package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Props, RootActorPath}
import akka.pattern.ask
import akka.util.Timeout
import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.core.demo.CassandraStoreDemo.level
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica._
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.{AkkaAddress, getActorSystemAddress}
import de.tuda.stg.consys.utils.Logger

import java.util.concurrent.TimeUnit
import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration.FiniteDuration
import scala.reflect.ClassTag
import scala.util.{Failure, Success, Try}

class BackendReplica(val system : ActorSystem, val timeout : FiniteDuration) {


	val replicaActor : ActorRef = system.actorOf(Props.apply(classOf[ReplicaActor]), AkkaStore.DEFAULT_ACTOR_NAME)
	Logger.info("created backend replica actor " + replicaActor.path.toString)


	private def addOtherReplica(otherActor : ActorRef) : Unit = {
		this.replicaActor ! AddReplica(otherActor)
	}

	private def addOtherReplica(path : ActorPath) : Unit = {
		//Skip adding the replica if the path is the path to the current replica
		if (path.address.host == getActorSystemAddress(system).host
			&& path.address.port == getActorSystemAddress(system).port) {
			return
		}

		val selection = system.actorSelection(path)

		//Search for the other replica until it is found or the timeout is reached
		val start = System.nanoTime()
		var loop = true
		while (loop) {
			val resolved : Future[ActorRef] = selection.resolveOne(timeout)

			//Wait for resolved to be ready
			Await.ready(selection.resolveOne(timeout), timeout)

			resolved.value match {
				case None =>
					Logger.err("Future not ready yet. But we waited for it to be ready. How?")

				case Some(Success(actorRef)) =>
					loop = false
					addOtherReplica(actorRef)

				case Some(Failure(exc)) =>
					if (System.nanoTime() > start + timeout.toNanos)
						throw new TimeoutException(s"actor path $path was not resolved in the given time ($timeout).")
			}
		}
	}

	def addOtherReplica(hostname : String, port : Int) : Unit = {
		val sysname = AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME
		val address = akka.actor.Address("akka", sysname, hostname, port)
		addOtherReplica(address)
	}

	def addOtherReplica(address : AkkaAddress) : Unit = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		addOtherReplica(RootActorPath(address) / "user" / AkkaStore.DEFAULT_ACTOR_NAME)
	}





	def write(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
		implicit val akkaTimeout : Timeout = timeout
		val result = replicaActor ? ExecuteBatch(timestamp, ops)
		Await.ready(result, timeout)
	}

	def read[T <: ObjType](addr : Addr, level : Level) : T  = {
		implicit val akkaTimeout : Timeout = timeout

		val startTime = System.nanoTime()
		var obj : Option[AkkaObject[T]] = None

		while (true) {
			val timeTaken = System.nanoTime() - startTime

			if (timeTaken > timeout.toNanos) {
				throw new TimeoutException(s"reference to $addr was not resolved")
			}

			val result = replicaActor ? ReadObject(addr, level)
			obj = Await.result(result, timeout - FiniteDuration(timeTaken, TimeUnit.NANOSECONDS) ).asInstanceOf[Try[AkkaObject[T]]].toOption

			if (obj.nonEmpty) {
				return obj.get.state
			}

			Thread.sleep(100)
		}

		throw new NotImplementedError()
	}


}

object BackendReplica {


	type Addr = String
	type ObjType = Serializable
	type Level = ConsistencyLevel[AkkaStore]

	case class WriteObjectsOp(objects : Map[Addr, (ObjType, Level)], waitFor : Int)
	case class SyncWrite(objects : Map[Addr, (ObjType, Level)])

	sealed trait TransactionOp
	case class CreateOrUpdateObject(addr : Addr, newState : ObjType, level : Level) extends TransactionOp

	sealed trait Op
	case class ExecuteBatch(timestamp : Long, ops : Seq[TransactionOp]) extends Op
	case class ReadObject(addr : Addr, level : Level) extends Op
	case class AddReplica(actor : ActorRef) extends Op
	case class SynchronizeChanges(changes : List[(Addr, ObjType, Level, Long)]) extends Op
	case object Loop extends Op


	class ReplicaActor extends Actor {
		Logger.info(s"created actor $self")

		/* The replicated objects stored by this replica */
		private val localObjects : mutable.HashMap[Addr, AkkaObject[_ <: ObjType]] = mutable.HashMap.empty

		/* The replica actors of all replicas in the system (can include self) */
		private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

		override def receive : Receive = { message =>
			Logger.info(s"received message $message")
			try {
				message match {

					case AddReplica(otherActor) =>
						otherReplicas.add(otherActor)
						Logger.info(s"added replica $otherActor to $self")

					case ExecuteBatch(timestamp, ops) =>
						Logger.info(s"execute batch on $self: $ops")
						/* Tracks the changes done by this batch */
						val changes = mutable.Map.empty[Addr, (Addr, ObjType, Level, Long)]

						ops.foreach {
							case CreateOrUpdateObject(addr, state, level) =>
								val newObject = putOrMerge(addr, state, level, timestamp)
								changes.put(addr, (newObject.addr, newObject.state, newObject.level, timestamp))
						}

						// Push changes to other replicas
						Logger.info(s"broadcast changes from $self")
						val changesMap = changes.values.toList
						otherReplicas.foreach { otherActor =>
							try {
								otherActor ! SynchronizeChanges(changesMap)
								sender() ! 42
							} catch {
								case e => e.printStackTrace()
							}
						}


					case SynchronizeChanges(changes) =>
						Logger.info(s"merge changes on $self: $changes")
						changes.foreach(change => {
							val (addr, state, level, timestamp) = change
							putOrMerge(addr, state, level, timestamp)
						})


					case ReadObject(addr, level) =>
						Logger.info(s"read object on $self: $addr")

						localObjects.get(addr) match {
							case None =>
								sender() ! Failure(new IllegalStateException(s"object $addr not found"))
							case Some(result) =>
								sender() ! Success(result) // Return local object
						}
				}
			} catch {
				case e => Logger.err(e.getMessage)
			}
		}

		/** Puts a new object into the local objects replica. If there was already an object, then it merges the objects.
		 * Merging is done by either calling the merge function of a mergeable data type, or overwriting.
		 *
		 * @return the new object stored at the location
		 */
		private def putOrMerge[T <: Serializable : ClassTag](addr : Addr, state : T, level : Level, timestamp : Long) : AkkaObject[T] = {
			val newObject = AkkaObject.create(addr, state, level, timestamp)

			localObjects.put(addr, newObject) match {
				case None => newObject
				case Some(oldObject : AkkaObject[T]) =>
					newObject.mergeWith(oldObject.state, timestamp)
					newObject
			}
		}
	}


}
