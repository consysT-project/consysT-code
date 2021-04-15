package de.tuda.stg.consys.core.store.akka

import java.util.concurrent.CountDownLatch
import java.util.concurrent.locks.{LockSupport, ReentrantLock}
import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, ExtendedActorSystem, Props, RootActorPath, Address => AkkaAddr}
import com.datastax.oss.driver.api.core.CqlSession
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.LockingStore.DistributedLock
import de.tuda.stg.consys.core.store.akka.AkkaStore.{AcquireHandler, ClearObjectsReplica, CreateObjectReplica, RemoveObjectReplica}
import de.tuda.stg.consys.core.store.akka.Requests.{AsynchronousRequest, CloseHandler, HandleRequest, InitHandler, NoAnswerRequest, RequestHandler, RequestHandlerImpl, SynchronousRequest}
import de.tuda.stg.consys.core.store.akka.levels.AkkaConsistencyLevel
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.extensions.store.{DistributedStore, DistributedZookeeperLockingStore, DistributedZookeeperStore, LockingStore}
import de.tuda.stg.consys.core.store.utils.Address
import java.net.InetSocketAddress
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry
import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.language.higherKinds
import scala.reflect.ClassTag
import scala.util.{Failure, Success}

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
trait AkkaStore extends DistributedStore
	with DistributedZookeeperStore
	with DistributedZookeeperLockingStore
{
	override type Id = AkkaStoreId

	override type Addr = String
	override type ObjType = java.io.Serializable

	override type TxContext = AkkaTransactionContext

	override type HandlerType[T <: ObjType] = AkkaObject[T]
	override type RefType[T <: ObjType] = AkkaRef[T]

	override type Level = AkkaConsistencyLevel


	/*The actor that is used to communicate with this replica.*/
	private[akka] final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	AkkaStore.defaultActorName)

	/*Other replicas known to this replica.*/
	private[akka] final val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

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

	override protected[store] def enref[T <: ObjType : ClassTag](obj : HandlerType[T]) : RefType[T] =
		new AkkaRef[T](obj.addr, obj.consistencyLevel)


	private[akka] def handlerFor(replicaRef : ActorRef) : RequestHandler[Addr] = {
		import akka.pattern.ask
		val response = replicaRef.ask(AcquireHandler)(timeout)
		val result = Await.result(response, timeout)
		result.asInstanceOf[RequestHandler[Addr]]
	}

	private[akka] def getActorSystemAddress : AkkaAddr =
		actorSystem.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress

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
			val resolved : Future[ActorRef] = selection.resolveOne(timeout)

			//Wait for resolved to be ready
			Await.ready(selection.resolveOne(timeout), timeout)

			resolved.value match {
				case None =>
					sys.error("Future not ready yet. But we waited for it to be ready. How?")

				case Some(Success(actorRef)) =>
					loop = false
					addOtherReplica(actorRef)

				case Some(Failure(exc)) =>
					if (System.nanoTime() > start + timeout.toNanos)
						throw new TimeoutException(s"actor path $replicaActorPath was not resolved in the given time ($timeout).")
			}

		}



	}

	private[akka] def addOtherReplica(hostname : String, port : Int) : Unit = {
		val sysname = AkkaStore.defaultSystemName
		val address = AkkaAddr("akka", sysname, hostname, port)
		addOtherReplica(address)
	}

	private[akka] def addOtherReplica(address : AkkaAddr) : Unit = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		addOtherReplica(RootActorPath(address) / "user" / AkkaStore.defaultActorName)
	}




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
				val ref = level.toProtocol(AkkaStore.this).createFollowerReplica(addr, obj, masterRef, null)(
					ClassTag(obj.getClass)
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

	private[AkkaStore] val defaultSystemName = "consys-replicas"
	private[AkkaStore] val defaultActorName = "replica-base"

	def fromAddress(host : String, akkaPort : Int, zookeeperPort : Int, others : Iterable[Address], withTimeout : FiniteDuration = Duration(30, "s")) : AkkaStore = {

		//Loads the reference.conf for the akka properties
		val config = ConfigFactory.load()
			.withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef(host))
			.withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(akkaPort))
			.resolve()

		//Creates the actor system
		val system = ActorSystem(defaultSystemName, config)
		system.log.info(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

		class AkkaStoreImpl(
			override val actorSystem : ActorSystem,
			override val curator : CuratorFramework,
			override val timeout : FiniteDuration
		) extends AkkaStore


		val store : AkkaStore = new AkkaStoreImpl(
			actorSystem = system,
			curator = CuratorFrameworkFactory
				.newClient(s"$host:$zookeeperPort", new ExponentialBackoffRetry(250, 3)),
			timeout = withTimeout
		)

		others.foreach(address => {
			store.addOtherReplica(address.hostname, address.port)
		})

		store
	}




	sealed trait ReplicaActorMessage
	case class CreateObjectReplica[Addr, L](addr : Addr, obj : Any, consistencyLevel : AkkaConsistencyLevel, masterRef : ActorRef) extends ReplicaActorMessage {
		require(obj.isInstanceOf[java.io.Serializable], s"expected serializable, but was $obj of class ${obj.getClass}")
	}

	case class RemoveObjectReplica[Addr](addr : Addr) extends ReplicaActorMessage
	case class ClearObjectsReplica[Addr](except : Set[Addr]) extends ReplicaActorMessage



	case object AcquireHandler extends ReplicaActorMessage

}
