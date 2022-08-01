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
import scala.util.{Failure, Success}

class BackendReplica(val system : ActorSystem, val timeout : FiniteDuration) {

	/*Other replicas known to this replica.*/


	private val actor : ActorRef = system.actorOf(Props.apply(classOf[ReplicaActor]), AkkaStore.DEFAULT_ACTOR_NAME)
	Logger.info("created backend replica actor " + actor.path.toString)

	private def addOtherReplica(actor : ActorRef) : Unit = {
		actor ! AddReplica(actor)
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
		actor ! ExecuteBatch(ops, pushChanges = true)

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

	def read[T <: ObjType](addr : Addr, level : Level) : AkkaObject[T]  = {
		implicit val akkaTimeout : Timeout = timeout
		val result = actor ? ReadObject(addr, level)

		val obj : AkkaObject[T] = Await.result(result, timeout).asInstanceOf[AkkaObject[T]]
		obj
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


	class ReplicaActor extends Actor {

		/* The replicated objects stored by this replica */
		private val localObjects : mutable.HashMap[Addr, AkkaObject[_ <: ObjType]] = mutable.HashMap.empty

		/* The replica actors of all replicas in the system (can include self) */
		private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

		override def receive : Receive = {
			case AddReplica(actor) =>
				otherReplicas.add(actor)

			case ExecuteBatch(ops, pushChanges) =>
				ops.foreach {
					case CreateObject(addr, state, level) =>
						if (localObjects.contains(addr))
							Logger.err("object already exists: " + addr)
						localObjects.put(addr, new AkkaObject(addr, state, level))

					case UpdateObject(addr, state, level) =>
						//TODO: Add merge semantics
						localObjects.put(addr, new AkkaObject(addr, state, level)) match {
						  case None =>
								Logger.err("object does not exist: " + addr)
						  case Some(obj) if obj.level != level =>
								Logger.err(s"object has wrong consistency level. expected : $level, but was ${obj.level}")
						  case Some(obj) =>
						}

					case CreateOrUpdateObject(addr, state, level) =>
					  localObjects.put(addr, new AkkaObject(addr, state, level)) match {
							case None =>
							case Some(obj) if obj.level != level =>
								Logger.err(s"object has wrong consistency level. expected : $level, but was ${obj.level}")
							case Some(obj) =>
					  }
				}
				if (pushChanges)
					otherReplicas.foreach(actor => actor ! ExecuteBatch(ops, false))


			case ReadObject(addr, level) =>
				val result = localObjects.getOrElse(addr, throw new IllegalStateException("object does not exist"))
				sender() ! result // Return local object
		}
	}


}
