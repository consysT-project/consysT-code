package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.{Actor, ActorRef}
import akka.util.Timeout
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.{SyncWrite, WriteObjectsOp}
import java.util.concurrent.CountDownLatch
import scala.collection.mutable
import scala.concurrent.duration.Duration
import scala.util.Success

class BackendReplica {

	type Addr
	type ObjType
	type Level







}

object BackendReplica {
	case class LocalObject[Addr, ObjType, Level](addr : Addr, state : ObjType, level : Level)

	case class WriteObjectsOp[Addr, ObjType, Level](objects : Map[Addr, (ObjType, Level)], waitFor : Int)
	case class SyncWrite[Addr, ObjType, Level](objects : Map[Addr, (ObjType, Level)])



	class MyActor[Addr, ObjType, Level] extends Actor {

		/*Other replicas known to this replica.*/
		private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

		/*The replicated objects stored by this replica*/
		private val localObjects : mutable.HashMap[Addr, LocalObject[Addr, ObjType, Level]] = mutable.HashMap.empty


		protected override def receive : Receive = {

			case WriteObjectsOp(objects, waitFor) =>
				objects.foreach(entry => {
					val (addr : Addr, (obj : ObjType, level : Level)) = entry
					localObjects.put(addr, LocalObject(addr, obj, level))
				})
				import akka.pattern.ask
				implicit val timeout : Timeout = Duration(30, "sec")

				val sent = new CountDownLatch(localObjects.size)
				val acked = new CountDownLatch(waitFor)


				otherReplicas.foreach { ref =>
					ask(ref, SyncWrite(objects)).andThen({
						case Success(any) =>
					})
				}







			case ReadObjects() =>
			case SyncRead() =>


		}
	}



}
