package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.pattern.ask
import akka.util.Timeout
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica._

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration.FiniteDuration

class BackendReplica(val system : ActorSystem, val timeout : FiniteDuration) {

	/*Other replicas known to this replica.*/
	private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	private val actor : ActorRef = system.actorOf(Props.apply(classOf[ReplicaActor]))


	def write(ops : Seq[TransactionOp]): Unit = {
		actor ! ExecuteBatch(ops)
		otherReplicas.foreach( a =>
			if (a != actor) a ! ExecuteBatch(ops)
		)

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
	case class ExecuteBatch(ops : Seq[TransactionOp]) extends Op
	case class ReadObject(addr : Addr, level : Level) extends Op


	class ReplicaActor extends Actor {

		/*The replicated objects stored by this replica*/
		private val localObjects : mutable.HashMap[Addr, AkkaObject[_ <: ObjType]] = mutable.HashMap.empty

		override def receive : Receive = {
			case ExecuteBatch(ops) =>
				ops.foreach {
					case CreateObject(addr, state, level) =>
						if (localObjects.contains(addr))
							throw new IllegalStateException("object already exists: " + addr)
						localObjects.put(addr, new AkkaObject(addr, state, level))

					case UpdateObject(addr, state, level) =>
						//TODO: Add merge semantics
						localObjects.put(addr, new AkkaObject(addr, state, level)) match {
						  case None => throw new IllegalStateException("object does not exist: " + addr)
						  case Some(obj) if obj.level != level => throw new IllegalStateException(s"object has wrong consistency level. expected : $level, but was ${obj.level}")
						  case Some(_) =>
						}

					case CreateOrUpdateObject(addr, state, level) =>
					  localObjects.put(addr, new AkkaObject(addr, state, level)) match {
						case None =>
						case Some(obj) if obj.level != level => throw new IllegalStateException(s"object has wrong consistency level. expected : $level, but was ${obj.level}")
						case Some(_) =>
					  }
				}

			case ReadObject(addr, level) =>
				val result = localObjects.getOrElse(addr, throw new IllegalStateException("object does not exist"))
				sender() ! result // Return local object
		}
	}


}
