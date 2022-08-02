package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Props, RootActorPath}
import akka.pattern.ask
import akka.util.Timeout
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica._
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils.{AkkaAddress, getActorSystemAddress}
import de.tuda.stg.consys.utils.Logger

import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration.FiniteDuration
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





	def write(ops : Seq[TransactionOp]): Unit = {

		implicit val akkaTimeout : Timeout = timeout

		val result = replicaActor ? ExecuteBatch(ops, pushChanges = true)

		Await.ready(result, timeout)


		//TODO: Synchronous write?
		//
		//	import akka.pattern.ask
		//	implicit val timeout : Timeout = Duration(30, "sec")
		//
		//	val sent = new CountDownLatch(localObjects.size)
		//	val acked = new CountDownLatch(waitFor)
		//
		//	otherReplicas.foreach { ref =>
		//					ask(ref, SyncWrite(objects)).andThen({
		//						case Success(any) =>
		//					})
		//	}
	}

	def read[T <: ObjType](addr : Addr, level : Level) : Option[AkkaObject[T]]  = {
		implicit val akkaTimeout : Timeout = timeout
		val result = replicaActor ? ReadObject(addr, level)

		val obj : Try[AkkaObject[T]] = Await.result(result, timeout).asInstanceOf[Try[AkkaObject[T]]]

		obj.toOption
	}


}

object BackendReplica {


	type Addr = String
	type ObjType = Serializable
	type Level = ConsistencyLevel[AkkaStore]

	case class WriteObjectsOp(objects : Map[Addr, (ObjType, Level)], waitFor : Int)
	case class SyncWrite(objects : Map[Addr, (ObjType, Level)])

	sealed trait TransactionOp
	case class CreateObject(addr : Addr, state : ObjType, level : Level) extends TransactionOp
	case class UpdateObject(addr : Addr, newState : ObjType, level : Level) extends TransactionOp
	case class CreateOrUpdateObject(addr : Addr, newState : ObjType, level : Level) extends TransactionOp

	sealed trait Op
	case class ExecuteBatch(ops : Seq[TransactionOp], pushChanges : Boolean) extends Op
	case class ReadObject(addr : Addr, level : Level) extends Op
	case class AddReplica(actor : ActorRef) extends Op
	case class SynchronizeChanges(changes : List[(Addr, ObjType, Level)]) extends Op
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

					case ExecuteBatch(ops, pushChanges) =>
						Logger.info(s"execute batch on $self: $ops")
						/* Tracks the changes done by this batch */
						val changes = mutable.Map.empty[Addr, AkkaObject[_ <: ObjType]]

						ops.foreach {
							case CreateObject(addr, state, level) =>
								if (localObjects.contains(addr))
									Logger.err("object already exists: " + addr)

								val newObject = new AkkaObject(addr, state, level)
								localObjects.put(addr, newObject)
								changes.put(addr, newObject)

							case UpdateObject(addr, state, level) =>
								//TODO: Add merge semantics
								val newObject = new AkkaObject(addr, state, level)
								localObjects.put(addr, newObject) match {
									case None =>
										Logger.err("object does not exist: " + addr)
									case Some(oldObject) if oldObject.level != level =>
										Logger.err(s"object has wrong consistency level. expected : ${oldObject.level}, but was $level")
									case Some(oldObject) =>
										changes.put(addr, newObject)
								}

							case CreateOrUpdateObject(addr, state, level) =>
								val newObject = AkkaObject(addr, state, level)
								localObjects.put(addr, newObject) match {
									case None =>
										changes.put(addr, newObject)
									case Some(oldObject) if oldObject.level != level =>
										Logger.err(s"object has wrong consistency level. expected : $level, but was ${oldObject.level}")
									case Some(oldObject) =>
										changes.put(addr, newObject)
								}
						}

						if (pushChanges) {
							Logger.info(s"send batch from $self")
							val changesMap = changes.values.map(obj => (obj.addr, obj.state, obj.level)).toList
							otherReplicas.foreach { otherActor =>
								try {
									Logger.info(s"synchronize from $self to $otherActor")
									otherActor ! SynchronizeChanges(changesMap)
									sender() ! 42
								} catch {
									case e => e.printStackTrace()
								}
							}
						}



					case SynchronizeChanges(changes) =>
						Logger.info(s"synchronized changes on $self: $changes")
						changes.foreach(change => {
							localObjects.put(change._1, AkkaObject(change._1, change._2, change._3))
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
	}


}
