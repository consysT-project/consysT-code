package de.tuda.stg.consys.core.legacy.akka

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, ExtendedActorSystem, Props, RootActorPath}
import akka.event.LoggingAdapter
import akka.util.Timeout
import akka.pattern.ask
import de.tuda.stg.consys.core.legacy
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem._
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystemFactory.AkkaReplicaSystemBinding
import de.tuda.stg.consys.core.legacy.akka.Requests._
import de.tuda.stg.consys.core.legacy._
import java.util.concurrent.CountDownLatch
import java.util.concurrent.locks.{LockSupport, ReentrantLock}
import scala.collection.mutable
import scala.concurrent.duration._
import scala.concurrent.{Await, Future, TimeoutException}
import scala.language.{higherKinds, postfixOps}
import scala.reflect.runtime.universe._
import scala.util.{Failure, Success}

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem extends ReplicaSystem
	with DeletableReplicaSystem
	with AkkaTransactionalReplicaSystem
	with BarrierReplicaSystem
	with LockServiceReplicaSystem
	with ReplicaSystemJavaBinding
{

	override type Obj = AnyRef with java.io.Serializable

	override type Tx = Transaction

	override type Ref[T <: Obj] <: AkkaRef[Addr, T]

	override type ConsistencyLevel = ConsistencyLabel

	/*The actor that is used to communicate with this replica.*/
	private final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	AkkaReplicaSystem.replicaActorName)

	/*Other replicas known to this replica.*/
	private final val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	private val barriers : collection.concurrent.TrieMap[String, CountDownLatch] =
		scala.collection.concurrent.TrieMap.empty[String, CountDownLatch]

	val defaultTimeout : FiniteDuration

	protected[akka] object replica {

		/*The replicated objects stored by this replica*/
		private final val localObjects : mutable.Map[Addr, AkkaReplicatedObject[Addr, _]] = mutable.HashMap.empty

		private final val waiters : mutable.MultiMap[Addr, Thread] = new mutable.HashMap[Addr, mutable.Set[Thread]] with mutable.MultiMap[Addr, Thread]
		private final val waitersLock : ReentrantLock = new ReentrantLock()

		def get(addr : Addr) : Option[AkkaReplicatedObject[Addr, _]] = {
			localObjects.get(addr)
		}
		def contains(addr : Addr) : Boolean = {
			localObjects.contains(addr)
		}
		def put(obj : AkkaReplicatedObject[Addr, _]) : Unit = {
			localObjects.put(obj.addr, obj) match {
				case Some(oldObj) if obj != oldObj =>
					oldObj.delete()
				case _ =>
			}
		}

		def size : Int = localObjects.valuesIterator.foldLeft(0)((i, obj) => if (obj.consistencyLevel == ConsistencyLabel.Strong) i + 1 else i)


		def remove(addr : Addr) : Unit = localObjects.remove(addr) match {
			case None =>
			case Some(obj) => obj.delete()
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
				case Some(obj) => obj.delete()
			})
		}

		def putNewReplica(obj : AkkaReplicatedObject[Addr, _]) : Unit = {
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

	def name : String = actorSystem.name


	def actorSystem : ActorSystem

	protected def freshAddr() : Addr

	protected def newRef[T <: Obj : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T]


	override def acquireLock(addr : Addr, tx : Transaction) : Unit = replica.get(addr) match {
		case None => sys.error(s"replicated object $addr not found.")
		case Some(rob :  Lockable[_]) =>
			rob.lock(tx.id)
		case Some(x) => sys.error(s"expected lockable replicated object, but got$x")
	}

	override def releaseLock(addr : Addr, tx : Transaction) : Unit = replica.get(addr) match {
		case None => sys.error(s"replicated object $addr not found.")
		case Some(rob :  Lockable[_]) => rob.unlock(tx.id)
		case Some(x) => sys.error(s"expected lockable replicated object, but got$x")
	}


	override final def replicate[T <: Obj : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T] = {
		require(!replica.contains(addr))

		/*create the replicated object*/
		val replicatedObject = createMasterReplica[T](l, addr, obj)

		/*put the object in the local replica store*/
		replica.put(replicatedObject)

		/*notify other replicas for the new object.*/
		implicit val timeout : Timeout = defaultTimeout
		val futures = otherReplicas.map { actorRef =>
			actorRef ? CreateObjectReplica(addr, obj, l, replicaActor)
		}
		futures.foreach { future => Await.ready(future, defaultTimeout) }

		/*create a ref to that object*/
		newRef[T](addr, l)
	}

	override final def delete(addr : Addr) : Unit = {
		require(replica.contains(addr))

		replica.remove(addr)

		implicit val timeout : Timeout = defaultTimeout
		val futures = otherReplicas.map(actorRef =>	actorRef ? RemoveObjectReplica(addr))
		futures.foreach { future => Await.ready(future, defaultTimeout) }
	}

	override def clear(except : Set[Addr] = Set.empty) : Unit = {
		replica.clear(except)

		/*notify other replicas for the new object.*/
//		implicit val timeout : Timeout = defaultTimeout
//		val futures = otherReplicas.map(actorRef =>	actorRef ? ClearObjectsReplica(except))
//		futures.foreach { future => Await.ready(future, defaultTimeout) }
	}


	def numberOfObjects: Int = replica.size


	override final def replicate[T <: Obj : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T] = {
		replicate[T](freshAddr(), obj, l)
	}

	override final def lookup[T <: Obj : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T] = {
		newRef[T](addr, l)
	}


	override def println(msg : String) : Unit = {
		actorSystem.log.info(msg)
	}

	protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")


	override def close() : Unit = {
		Await.ready(actorSystem.terminate(), defaultTimeout)
	}




	override def barrier(name : String, timeout : Duration) : Unit = {
		//Wait for other barrier objects
		val latch = barriers.getOrElseUpdate(name, new CountDownLatch(otherReplicas.size))

		otherReplicas.foreach(actorRef => actorRef ! EnterBarrier(name))

		val countedDown = latch.await(timeout.toMillis, java.util.concurrent.TimeUnit.MILLISECONDS)
		if (!countedDown) throw new TimeoutException(s"barrier $name did timeout.")
		barriers.remove(name)
	}

	def barrier(name : String) : Unit = barrier(name, defaultTimeout)


	def getName : String = getActorSystemAddress.toString


	/*writes a message to the standard out*/
	protected[akka] def log : LoggingAdapter = actorSystem.log

	private[akka] def getActorSystemAddress : Address =
		actorSystem.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress

	/**
	 * @return Set of ReplicaActor
	 */
	def getOtherReplicas : Set[ActorRef] = {
		otherReplicas.toSet
	}

	private def addOtherReplica(replicaActorRef : ActorRef) : Unit = {
		otherReplicas.add(replicaActorRef)
	}

	private[akka] def addOtherReplica(replicaActorPath : ActorPath) : Unit = {

		//Skip adding the replica if the path is the path to the current replica
		if (replicaActorPath.address.host == getActorSystemAddress.host
			&& replicaActorPath.address.port == getActorSystemAddress.port) {
			return
		}


		val selection = actorSystem.actorSelection(replicaActorPath)

		//Search for the other replica until it is found or the timeout is reached
		val start = System.nanoTime()
		var loop = true
		while (loop) {
			val resolved : Future[ActorRef] = selection.resolveOne(defaultTimeout)

			//Wait for resolved to be ready
			Await.ready(selection.resolveOne(defaultTimeout), defaultTimeout)

			resolved.value match {
				case None =>
					sys.error("Future not ready yet. But we waited for it to be ready. How?")

				case Some(Success(actorRef)) =>
					loop = false
					addOtherReplica(actorRef)

				case Some(Failure(exc)) =>
					if (System.nanoTime() > start + defaultTimeout.toNanos)
						throw new TimeoutException(s"actor path $replicaActorPath was not resolved in the given time ($defaultTimeout).")
			}

		}



	}

	private[akka] def addOtherReplica(hostname : String, port : Int) : Unit = {
		val sysname = DEFAULT_ACTORSYSTEM_NAME
		val address = Address("akka", sysname, hostname, port)
		addOtherReplica(address)
	}

	private[akka] def addOtherReplica(address : Address) : Unit = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		addOtherReplica(RootActorPath(address) / "user" / AkkaReplicaSystem.replicaActorName)
	}


	private[akka] def handlerFor(replicaRef : ActorRef) : RequestHandler[Addr] = {
		val response = replicaRef.ask(AcquireHandler)(defaultTimeout)
		val result = Await.result(response, defaultTimeout)
		result.asInstanceOf[RequestHandler[Addr]]
	}

	private[akka] def foreachOtherReplica(f : RequestHandler[Addr] => Unit) : Unit = {
		for (replica <- otherReplicas) {
			val handler = handlerFor(replica)
			f(handler)
			handler.close()
		}
	}


	/**
		* Recursively initializes all fields of an object that store a Ref.
		* Initializing means, setting the replica system of the ref.
		*
		* @param obj
		*/
	private[akka] def initializeRefFields(obj : Any) : Unit = {

		def initializeObject(any : Any, alreadyInitialized : Set[Any]) : Unit = {
			//If the object is null, there is nothing to initialize
			//If the object has already been initialized than stop
			if (any == null || alreadyInitialized.contains(any)) {
				return
			}

			any match {
				//If the object is a RefImpl
				case refImpl : AkkaRef[Addr, _] =>
					AkkaReplicaSystems.setSystem(this.asInstanceOf[AkkaReplicaSystemBinding])

				//The object is a ref, but is not supported by the replica system
				case ref :  legacy.Ref[_, _] =>
					sys.error(s"cannot initialize unknown implementation of Ref. $ref : ${ref.getClass}")

				case _ =>

					val anyClass = any.getClass
					//If the value is primitive (e.g. int) then stop
					if (anyClass.isPrimitive) {
						return
					}

					//If the value is an array, then initialize ever element of the array.
					if (anyClass.isArray) {
						val anyArray : Array[_] = any.asInstanceOf[Array[_]]
						val initSet = alreadyInitialized + any
						anyArray.foreach(e => initializeObject(e, initSet))
					}


					val anyPackage = anyClass.getPackage
					//Check that the object has a package declaration and that it is not the Java standard library
					if (anyPackage == null || anyPackage.getImplementationTitle == "Java Runtime Environment" || anyPackage.getName.startsWith("java")) {
						return
					}

					//If the object should be initialized, then initialize all fields
					anyClass.getDeclaredFields.foreach { field =>
						//Recursively initialize refs in the fields
						field.setAccessible(true)
						val fieldObj = field.get(any)
						initializeObject(fieldObj, alreadyInitialized + any)
					}
			}
		}

		initializeObject(obj, Set.empty)
	}


	private class ReplicaActor extends Actor {

		override def receive : Receive = {
			case CreateObjectReplica(addr : Addr@unchecked, obj : Obj, consistencyLevel, masterRef) =>
				/*Initialize a new replicated object on this host*/
				//Ensure that no object already exists under this name
				require(!replica.contains(addr), s"address $addr is already defined")

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplica(consistencyLevel, addr, obj, masterRef)(
					ConsysUtils.typeTagFromCls(obj.getClass.asInstanceOf[Class[Obj]])
				)
				replica.putNewReplica(ref)
				sender() ! ()

			case RemoveObjectReplica(addr : Addr@unchecked) =>
				require(replica.contains(addr))
				replica.remove(addr)
				sender() ! ()

			case ClearObjectsReplica(except) =>
				replica.clear(except.asInstanceOf[Set[Addr]])
				sender() ! ()

			case AcquireHandler =>
				val requestActor = context.actorOf(Props(classOf[RequestHandlerActor], this).withDispatcher("request-dispatcher"))
				val handler = new RequestHandlerImpl(requestActor, self, defaultTimeout)
				sender() ! handler

			case EnterBarrier(name) =>
				val latch = barriers.getOrElseUpdate(name, new CountDownLatch(otherReplicas.size))
				latch.countDown()
		}

		private class RequestHandlerActor extends Actor {

			override def receive : Receive = {
				case InitHandler =>
					clearTransaction()
					()

				case HandleRequest(addr : Addr@unchecked, request) =>	replica.get(addr) match {
					case None => sys.error(s"object $addr not found")
					case Some(obj) => request match {
						case _ : SynchronousRequest[_] | _ : AsynchronousRequest[_] =>
							sender() ! obj.handleRequest(request)
						case _ : NoAnswerRequest =>
							obj.handleRequest(request)
					}
				}

				case CloseHandler =>
					clearTransaction()
					context.stop(self)
			}
		}
	}
}

object AkkaReplicaSystem {

	private final val replicaActorName : String = "replica-base"

	sealed trait ReplicaActorMessage
	case class CreateObjectReplica[Addr, L](addr : Addr, obj : Any, consistencyLevel : ConsistencyLabel, masterRef : ActorRef) extends ReplicaActorMessage {
		require(obj.isInstanceOf[java.io.Serializable], s"expected serializable, but was $obj of class ${obj.getClass}")
	}

	case class RemoveObjectReplica[Addr](addr : Addr) extends ReplicaActorMessage
	case class ClearObjectsReplica[Addr](except : Set[Addr]) extends ReplicaActorMessage
	case class EnterBarrier(name : String) extends ReplicaActorMessage



	case object AcquireHandler extends ReplicaActorMessage

}









