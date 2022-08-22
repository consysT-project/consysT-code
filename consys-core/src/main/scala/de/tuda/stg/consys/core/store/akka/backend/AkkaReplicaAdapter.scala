package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Props, RootActorPath}
import akka.cluster.ddata.{DistributedData, Replicator}
import akka.pattern.ask
import akka.util.Timeout
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter._
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.{AkkaAddress, getActorSystemAddress}
import de.tuda.stg.consys.core.store.extensions.coordination.DistributedLock
import org.apache.curator.framework.CuratorFramework
import org.apache.curator.framework.recipes.locks.InterProcessMutex
import akka.cluster.ddata.typed.scaladsl.Replicator._
import de.tuda.stg.consys.logging.Logger

import java.util.UUID
import java.util.concurrent.TimeUnit
import scala.collection.mutable
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Future, TimeoutException}
import scala.reflect.ClassTag
import scala.util.{Failure, Success, Try}

private[akka] class AkkaReplicaAdapter(val system : ActorSystem, val curator : CuratorFramework, val timeout : FiniteDuration) {

	val replicaActor : ActorRef = system.actorOf(Props.apply(classOf[ReplicaActor], timeout), AkkaStore.DEFAULT_ACTOR_NAME)

	private def addOtherReplica(otherActor : ActorRef) : Unit = {
		this.replicaActor ! AddReplica(otherActor)
	}

	private def addOtherReplicaAsync(path : ActorPath) : Future[Unit] = {
		//Skip adding the replica if the path is the path to the current replica
		if (path.address.host == getActorSystemAddress(system).host
			&& path.address.port == getActorSystemAddress(system).port) {
			return Future.successful(())
		}

		val selection = system.actorSelection(path)

		selection.resolveOne(timeout).transform(result => {
			result match {
				case Success(actorRef) =>
					addOtherReplica(actorRef)
					Success(())
				case Failure(exc) =>
					//TODO: Implement correct error handling
					Logger.err(s"actor path $path was not resolved. Cause: ${exc.toString} ")
					Failure(new IllegalStateException(s"actor path $path was not resolved in the given time ($timeout). Cause: ${exc.toString} "))
			}
		})(system.dispatchers.defaultGlobalDispatcher)


		//Search for the other replica until it is found or the timeout is reached

	}

	def addOtherReplicaAsync(hostname : String, port : Int) : Future[Unit] = {
		val sysname = AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME
		val address = akka.actor.Address("akka", sysname, hostname, port)
		addOtherReplicaAsync(address)
	}

	def addOtherReplicaAsync(address : AkkaAddress) : Future[Unit] = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		val path : ActorPath = RootActorPath(address) / "user" / AkkaStore.DEFAULT_ACTOR_NAME
		addOtherReplicaAsync(path)
	}

	def addOtherReplica(address : AkkaAddress) : Unit = {
		val start = System.nanoTime()
		var loop = true
		while (loop) {
			val replicaResolved : Future[Unit] = addOtherReplicaAsync(address)

			//Wait for resolved to be ready
			Await.ready(replicaResolved, timeout)

			replicaResolved.value match {
				case None =>
					throw new IllegalStateException("Future not ready yet. But we waited for it to be ready. How?")

				case Some(Success(())) =>
					// We are done. We can leave the loop.
					loop = false

				case Some(Failure(exc)) =>
					if (System.nanoTime() > start + timeout.toNanos) {
						// Throw an exception if timeout, else try to resolve the path again
						throw new TimeoutException(s"actor $address was not resolved in the given time ($timeout). Cause: ${exc.toString} ")
					}
			}
		}
	}

	def addOtherReplica(hostname : String, port : Int) : Unit = {
		val sysname = AkkaStore.DEFAULT_ACTOR_SYSTEM_NAME
		val address = akka.actor.Address("akka", sysname, hostname, port)
		addOtherReplica(address)
	}

	def writeAsync(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
		implicit val akkaTimeout : Timeout = timeout
		val result = replicaActor ? ExecuteBatchAsync(timestamp, ops)
		Await.ready(result, timeout)
	}

	def writeSync(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
		implicit val akkaTimeout : Timeout = timeout
		val result = replicaActor ? ExecuteBatchSync(timestamp, ops)
		Await.ready(result, timeout)
	}

	def read[T <: ObjType](addr : Addr) : T  = {
		implicit val akkaTimeout : Timeout = timeout

		val startTime = System.nanoTime()
		var obj : Option[AkkaObject[T]] = None

		while (true) {
			val timeTaken = System.nanoTime() - startTime

			if (timeTaken > timeout.toNanos) {
				throw new TimeoutException(s"reference to $addr was not resolved")
			}

			val result = replicaActor ? ReadObject(addr)
			obj = Await.result(result, timeout - FiniteDuration(timeTaken, TimeUnit.NANOSECONDS) ).asInstanceOf[Try[AkkaObject[T]]].toOption

			if (obj.nonEmpty) {
				return obj.get.state
			}

			Thread.sleep(100)
		}

		throw new NotImplementedError()
	}

	def clear() : Unit = {
		implicit val akkaTimeout : Timeout = timeout
		val result = replicaActor ? ClearStore
		Await.ready(result, timeout)
	}

	def close() : Unit = {
		replicaActor ! TerminateStore
	}



}

object AkkaReplicaAdapter {


	type Addr = String
	type ObjType = Serializable

	/* A list of changes of the replica. Each change has a key, new state, consistency level, and timestamp */
	type ChangeList = Iterable[(Addr, ObjType, Long)]


	sealed trait TransactionOp
	case class CreateOrUpdateObject(addr : Addr, newState : ObjType) extends TransactionOp

	sealed trait Op
	case class ExecuteBatchAsync(timestamp : Long, ops : Seq[TransactionOp]) extends Op
	case class ExecuteBatchSync(timestamp : Long, ops : Seq[TransactionOp]) extends Op
	case class ReadObject(addr : Addr) extends Op
	case class AddReplica(actor : ActorRef) extends Op
	case class PushChangesAsync(changes : ChangeList) extends Op
	case class PrepareChangesSync(key : String, changes : ChangeList) extends Op
	case class CommitChanges(key : String) extends Op
	case object ClearStore extends Op
	case object TerminateStore extends Op


	class ReplicaActor(val timeout : FiniteDuration) extends Actor {
		/* The replicated objects stored by this replica */
		private val localObjects : mutable.HashMap[Addr, AkkaObject[_ <: ObjType]] = mutable.HashMap.empty

		/* Changes that are prepared for a commit, but have not been committed yet. */
		private val preparedChanges : mutable.HashMap[String, ChangeList] = mutable.HashMap.empty

		// TODO: Can we use replicated data instead?
		// private val replicatedData = DistributedData.apply(context.system).selfUniqueAddress

		/* The replica actors of all replicas in the system (can include self) */
		private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty


		override def receive : Receive = { message =>
			try {
				message match {

					case AddReplica(otherActor) =>
						otherReplicas.add(otherActor)

					/* Protocol for asynchronous writes */
					case ExecuteBatchAsync(timestamp, ops) =>
						// Apply the operations in the batch
						val changes = applyBatch(timestamp, ops)

						// Push changes to the other replicas
						otherReplicas.filter(ref => ref != self).foreach { otherActor =>
								otherActor ! PushChangesAsync(changes)
						}
						sender() ! "ack"

					case PushChangesAsync(changes) =>
						changes.foreach(change => {
							val (addr, state, timestamp) = change
							putOrMerge(addr, state, timestamp)
						})

					/* Protocol for synchronous writes */
					case ExecuteBatchSync(timestamp, ops) =>
						// Apply the operations in the batch
						val changes = applyBatch(timestamp, ops)


						implicit val akkaTimeout : Timeout = timeout
						// The key for the commit
						val key = context.system.name + "::" + UUID.randomUUID().toString

						val receivingReplicas = otherReplicas.filter(ref => ref != self)

						val prepared = receivingReplicas.map { otherActor =>
							otherActor ? PrepareChangesSync(key,changes)
						}

						prepared.foreach(future => Await.ready(future, timeout))

						val committed = receivingReplicas.map { otherActor =>
							otherActor ? CommitChanges(key)
						}

						committed.foreach(future => Await.ready(future, timeout))

						sender() ! "ack"

					case PrepareChangesSync(key, changes) =>
						preparedChanges.put(key, changes)
						sender() ! "ack"

					case CommitChanges(key) =>
						preparedChanges.get(key) match {
							case Some(changes) =>
								changes.foreach(change => {
									val (addr, state, timestamp) = change
									putOrMerge(addr, state, timestamp)
								})
							case None => Logger.err(s"cannot commit changes $key")
						}

						preparedChanges.remove(key)

						sender() ! "ack"




					case ReadObject(addr) =>
						localObjects.get(addr) match {
							case None =>
								sender() ! Failure(new IllegalStateException(s"object $addr not found"))
							case Some(result) =>
								sender() ! Success(result) // Return local object
						}

					case ClearStore =>
						localObjects.clear()
						sender() ! "ack"

					case TerminateStore =>
						context.system.terminate()
				}
			} catch {
				case e : Throwable => Logger.err(self, e.getMessage)
			}
		}

		/** Puts a new object into the local objects replica. If there was already an object, then it merges the objects.
		 * Merging is done by either calling the merge function of a mergeable data type, or overwriting.
		 *
		 * @return the new object stored at the location
		 */
		private def putOrMerge[T <: Serializable : ClassTag](addr : Addr, state : T, timestamp : Long) : AkkaObject[T] = {
			val newObject = AkkaObject.create(addr, state, timestamp)

			localObjects.put(addr, newObject) match {
				case None => newObject
				case Some(oldObject : AkkaObject[T]) =>
					newObject.mergeWith(oldObject.state, timestamp)
					newObject
			}
		}

		private def applyBatch(timestamp : Long, ops : Seq[TransactionOp]): ChangeList = {
			/* Tracks the changes done by this batch */
			val changes = mutable.Map.empty[Addr, (Addr, ObjType, Long)]

			try {
				ops.foreach {
					case CreateOrUpdateObject(addr, state) =>
						val newObject = putOrMerge(addr, state, timestamp)
						changes.put(addr, (newObject.addr, newObject.state, timestamp))
				}
			} catch {
				case e =>
					e.printStackTrace()
			}

			// Push changes to other replicas
			changes.values
		}

	}


}
