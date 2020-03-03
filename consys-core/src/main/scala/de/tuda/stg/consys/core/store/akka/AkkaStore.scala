package de.tuda.stg.consys.core.store.akka

import java.util.concurrent.CountDownLatch
import java.util.concurrent.locks.{LockSupport, ReentrantLock}

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import de.tuda.stg.consys.core.store.{DistributedStore, LockingStore}
import de.tuda.stg.consys.core.store.akka.AkkaStore.{AcquireHandler, ClearObjectsReplica, CreateObjectReplica, EnterBarrier, RemoveObjectReplica}
import de.tuda.stg.consys.core.store.akka.Requests.{AsynchronousRequest, CloseHandler, HandleRequest, InitHandler, NoAnswerRequest, RequestHandlerImpl, SynchronousRequest}
import de.tuda.stg.consys.core.store.akka.levels.AkkaConsistencyLevel

import scala.collection.mutable
import scala.language.higherKinds
import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
trait AkkaStore extends DistributedStore with LockingStore {
	override type Id = AkkaStoreId

	override type Addr = String
	override type ObjType = java.io.Serializable

	override type TxContext = AkkaTransactionContext

	override type RawType[T <: ObjType] = AkkaObject[T]
	override type RefType[T <: ObjType] = AkkaHandler[T]

	override type Level = AkkaConsistencyLevel


	/*The actor that is used to communicate with this replica.*/
	private[akka] final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	"replica-base")

	/*Other replicas known to this replica.*/
	private[akka] final val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	private val barriers : collection.concurrent.TrieMap[String, CountDownLatch] =
		scala.collection.concurrent.TrieMap.empty[String, CountDownLatch]

	protected[akka]	def actorSystem : ActorSystem

	override def id : Id = AkkaStoreId(s"akka-store@${actorSystem.name}")

	override def transaction[T](code : TxContext => Option[T]) : Option[T] = {
		AkkaStores.currentStore.withValue(this) {
			val tx = AkkaTransactionContext(this)
			AkkaStores.currentTransaction.withValue(tx) {
				try {
					code(tx) match {
						case None => None
						case res@Some(_) =>
							res
					}
				} finally {
					tx.commit()
				}
			}
		}

	}

	override protected[store] def enref[T <: ObjType : ClassTag](obj : RawType[T]) : RefType[T] =
		new AkkaHandler[T](obj.addr, obj.consistencyLevel)




	protected[akka] object LocalReplica {
		/*The replicated objects stored by this replica*/
		private final val localObjects : mutable.Map[Addr, AkkaObject[_]] = mutable.HashMap.empty

		private final val waiters : mutable.MultiMap[Addr, Thread] = new mutable.HashMap[Addr, mutable.Set[Thread]] with mutable.MultiMap[Addr, Thread]
		private final val waitersLock : ReentrantLock = new ReentrantLock()

		def get(addr : Addr) : Option[AkkaObject[_]] = {
			localObjects.get(addr)
		}

		def contains(addr : Addr) : Boolean = {
			localObjects.contains(addr)
		}

		def put(obj : AkkaObject[_]) : Unit = {
			localObjects.put(obj.addr, obj) match {
				case Some(oldObj) if obj != oldObj =>
//					oldObj.delete()
				case _ =>
			}
		}

//		def size : Int = localObjects.valuesIterator.foldLeft(0)((i, obj) => if (obj.consistencyLevel == ConsistencyLabel.Strong) i + 1 else i)


		def remove(addr : Addr) : Unit = localObjects.remove(addr) match {
			case None =>
//			case Some(obj) => obj.delete()
		}

		def waitFor(addr : Addr) : Unit = {
			waitersLock.lock()
			if (localObjects.contains(addr)) {
				waitersLock.unlock()
			} else {
				waiters.addBinding(addr, Thread.currentThread())
				waitersLock.unlock()
				LockSupport.park(Thread.currentThread())
			}
		}

		def clear(except : Set[Addr]) : Unit = {
			localObjects.keysIterator.filter(key => !except.contains(key)).foreach(key => localObjects.remove(key) match {
				case None =>
//				case Some(obj) => obj.delete()
			})
		}

		def putNewReplica(obj : AkkaObject[_]) : Unit = {
			waitersLock.lock()
			localObjects.put(obj.addr, obj)
			waiters.get(obj.addr) match {
				case None =>
				case Some(threads) =>
					threads.foreach(thread => LockSupport.unpark(thread))
					waiters.remove(obj.addr)
			}
			waitersLock.unlock()
		}
	}

	private class ReplicaActor extends Actor {

		override def receive : Receive = {
			case CreateObjectReplica(addr : Addr@unchecked, obj : ObjType, level, masterRef) =>
				/*Initialize a new replicated object on this host*/
				//Ensure that no object already exists under this name
				require(!LocalReplica.contains(addr), s"address $addr is already defined")

				//Create the replicated object on this replica and add it to the object map
				val ref = level.toModel(AkkaStore.this).createFollowerReplica(addr, obj, masterRef, null)(
					ClassTag(obj.getClass.asInstanceOf)
				)
				LocalReplica.putNewReplica(ref)
				sender() ! ()

			case RemoveObjectReplica(addr : Addr@unchecked) =>
				require(LocalReplica.contains(addr))
				LocalReplica.remove(addr)
				sender() ! ()

			case ClearObjectsReplica(except) =>
				LocalReplica.clear(except.asInstanceOf[Set[Addr]])
				sender() ! ()

			case AcquireHandler =>
				val requestActor = context.actorOf(Props(classOf[RequestHandlerActor], this).withDispatcher("request-dispatcher"))
				val handler = new RequestHandlerImpl(requestActor, timeout)
				sender() ! handler

			case EnterBarrier(name) =>
				val latch = barriers.getOrElseUpdate(name, new CountDownLatch(otherReplicas.size))
				latch.countDown()
		}

		private class RequestHandlerActor extends Actor {

			override def receive : Receive = {
				case InitHandler =>
					AkkaStores.currentTransaction.value = null
					AkkaStores.currentStore.value = AkkaStore.this
					()

				case HandleRequest(addr : Addr@unchecked, request) =>	LocalReplica.get(addr) match {
					case None => sys.error(s"object $addr not found")
					case Some(obj) => request match {
						case _ : SynchronousRequest[_] | _ : AsynchronousRequest[_] =>
							sender() ! obj.handleRequest(request)
						case _ : NoAnswerRequest =>
							obj.handleRequest(request)
					}
				}

				case CloseHandler =>
					AkkaStores.currentTransaction.value = null
					AkkaStores.currentStore.value = AkkaStore.this
					context.stop(self)
			}
		}
	}

}


object AkkaStore {
	sealed trait ReplicaActorMessage
	case class CreateObjectReplica[Addr, L](addr : Addr, obj : Any, consistencyLevel : AkkaConsistencyLevel, masterRef : ActorRef) extends ReplicaActorMessage {
		require(obj.isInstanceOf[java.io.Serializable], s"expected serializable, but was $obj of class ${obj.getClass}")
	}

	case class RemoveObjectReplica[Addr](addr : Addr) extends ReplicaActorMessage
	case class ClearObjectsReplica[Addr](except : Set[Addr]) extends ReplicaActorMessage
	case class EnterBarrier(name : String) extends ReplicaActorMessage



	case object AcquireHandler extends ReplicaActorMessage

}
