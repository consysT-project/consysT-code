package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorRef}
import akka.util.Timeout
import de.tuda.stg.consys.Mergeable
import java.util.concurrent.CountDownLatch
import scala.collection.mutable
import scala.concurrent.duration.Duration
import scala.util.Success

abstract class BackendReplica {

	type Addr
	type ObjType <: Mergeable[ObjType]
	type Level

	case class LocalObject(addr : Addr, state : ObjType, level : Level) {
		def merge(newState : ObjType) : LocalObject =
			LocalObject(addr, state, level)
	}

	case class WriteObjectsOp(objects : Map[Addr, (ObjType, Level)], waitFor : Int)
	case class SyncWrite(objects : Map[Addr, (ObjType, Level)])

	sealed trait TransactionOp
	case class CreateObject(addr : Addr, state : ObjType, level : Level) extends TransactionOp
	case class UpdateObject(addr : Addr, newState : ObjType, level : Level) extends TransactionOp

	case class ExecuteTransaction(ops : Seq[TransactionOp])


	/*Other replicas known to this replica.*/
	private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

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


	class ReplicaActor extends Actor {



		/*The replicated objects stored by this replica*/
		private val localObjects : mutable.HashMap[Addr, LocalObject] = mutable.HashMap.empty


		override def receive : Receive = {
			case ExecuteTransaction(ops) =>
				ops.foreach {
					case CreateObject(addr, state, level) =>
						if (localObjects.contains(addr))
							throw new IllegalStateException("object already exists: " + addr)
						localObjects.put(addr, new LocalObject(addr, state, level))

//					case
				}
//			case ReadObjects() =>
//			case SyncRead() =>


		}
	}



}
