package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, Props, RootActorPath}
import akka.remote.WireFormats.TimeUnit
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.ContextPath.ContextPathTracker
import de.tudarmstadt.consistency.replobj.actors.Requests._
import de.tudarmstadt.consistency.replobj.{ConsistencyLevel, Ref, ReplicaSystem, ReplicatedObject, Utils}

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.{DynamicVariable, Random}

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem[Addr] extends ReplicaSystem[Addr] {

  def actorSystem : ActorSystem

	protected def freshAddr() : Addr

	/*The replicated objects stored by this replica*/
	private final val localObjects : mutable.Map[Addr, AkkaReplicatedObject[Addr, _]] = mutable.HashMap.empty

	/*The actor that is used to communicate with this replica.*/
	private final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	AkkaReplicaSystem.replicaActorName)

	/*Other replicas known to this replica.*/
	private final val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	/*The current global context of this replica. The context is different for each thread that is accessing it.*/
	protected[actors] object GlobalContext {
		private val builder : DynamicVariable[Option[ContextPathTracker]] = new DynamicVariable(None)

		private def setBuilder(builder: ContextPathTracker) : Unit = {
			this.builder.value = Some(builder)
		}

		private[AkkaReplicaSystem] def resetBuilder() : Unit = {
			this.builder.value = None
		}

		def getBuilder : ContextPathTracker = {
			require(hasCurrentTransaction)
			builder.value.get
		}

		/**
			* Checks whether there is an active transaction on the
			* @return
			*/
		def hasCurrentTransaction : Boolean =
			builder.value.nonEmpty


		def startNewTransaction() : Unit = {
			require(!hasCurrentTransaction)
			val txid = Random.nextLong
			setBuilder(new ContextPathTracker(txid))
		}

		def endTransaction() : Unit = {
			require(hasCurrentTransaction)
			resetBuilder()
		}

		def setCurrentTransaction(path : ContextPath) : Unit = {
			require(!hasCurrentTransaction)
			setBuilder(new ContextPathTracker(path))
		}

		override def toString : String = s"context($builder)"
	}


	override final def replicate[T <: AnyRef : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T] = {
		require(!localObjects.contains(addr))

		import akka.pattern.ask

		/*create the replicated object*/
		val rob = createMasterReplica[T](l, addr, obj)
		/*put the object in the local replica store*/
		localObjects.put(addr, rob)

		/*notify other replicas for the new object.*/
		implicit val timeout : Timeout = Timeout(30L, SECONDS)
		val futures = otherReplicas.map(actorRef =>	actorRef ? CreateObjectReplica(addr, obj, l, replicaActor))

		futures.foreach { future => Await.ready(future, Duration(30L, SECONDS)) }

		/*create a ref to that object*/
		createRef(addr, l)
	}


	override final def replicate[T <: AnyRef : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T] = {
		replicate[T](freshAddr(), obj, l)
	}

	override final def ref[T <: AnyRef : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T] = {
		createRef(addr, l)
	}


	protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")


	override def close() : Unit = {
		Await.ready(actorSystem.terminate(), 30 seconds)
	}


	/*writes a message to the standard out*/
	private[actors] final def log(msg : String) : Unit = {
		val thisString = toString
		val printString = thisString.substring(thisString.indexOf("$"))
		println(s"[$printString] $msg")
	}




	private def addOtherReplica(replicaActorRef : ActorRef) : Unit = {
		otherReplicas.add(replicaActorRef)
	}

	def addOtherReplica(replicaActorPath : ActorPath) : Unit = {
		import scala.concurrent.duration._

		val selection = actorSystem.actorSelection(replicaActorPath)
		val actorRef = Await.result(selection.resolveOne(5 seconds), 5 seconds)

		addOtherReplica(actorRef)
	}

	def addOtherReplica(hostname : String, port : Int) : Unit = {
		val sysname = DEFAULT_ACTORSYSTEM_NAME
		val address = Address("akka.tcp", sysname, hostname, port)
		addOtherReplica(address)
	}

	def addOtherReplica(address : Address) : Unit = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		addOtherReplica(RootActorPath(address) / "user" / AkkaReplicaSystem.replicaActorName)
	}


	def acquireHandlerFrom(replicaRef : ActorRef, receiveTimeout : FiniteDuration = 30 seconds) : RequestHandler[Addr] = {
		import akka.pattern.ask
		val response = replicaRef.ask(AcquireHandler)(Timeout(receiveTimeout))
		val result = Await.result(response, receiveTimeout)
		result.asInstanceOf[RequestHandler[Addr]]
	}


	def initializeRefFieldsFor(obj : Any) : Unit = {

		def initializeObject(any : Any, alreadyInitialized : Set[Any]) : Unit = {
			//If the object is null, there is nothing to initialize
			//If the object has already been initialized than stop
			if (any == null || alreadyInitialized.contains(any)) {
				return
			}

			any match {
				//If the object is a RefImpl
				case refImpl : RefImpl[Addr, _] =>
					refImpl.replicaSystem = this

				//The object is a ref, but is not supported by the replica system
				case ref : Ref[_] =>
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
					if (anyPackage == null || anyPackage.getImplementationTitle == "Java Runtime Environment") {
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


	private def createRef[T <: AnyRef](addr : Addr, consistencyLevel : ConsistencyLevel) : RefImpl[Addr, T] = {
		new RefImpl[Addr, T](addr, consistencyLevel, this)
	}




	private class ReplicaActor extends Actor {

		override def receive : Receive = {
			case CreateObjectReplica(addr : Addr, obj, consistencyLevel, masterRef) =>
				/*Initialize a new replicated object on this host*/
				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr), s"address $addr is already defined")
				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplica(consistencyLevel, addr, obj, masterRef)(
					Utils.typeTagFromCls(obj.getClass.asInstanceOf[Class[AnyRef]])
				)
				localObjects.put(addr, ref)
				sender() ! ()

			case AcquireHandler =>
				val requestActor = context.actorOf(Props(classOf[RequestHandlerActor], this).withDispatcher("request-dispatcher"))
				val handler = new RequestHandlerImpl(requestActor)
				sender() ! handler
		}

		private class RequestHandlerActor extends Actor {

			override def receive : Receive = {
				case InitHandler => if (GlobalContext.hasCurrentTransaction) {
					//Ends a transaction that might be present from an previous RequestHandlerActor that was
					//executed on this thread. TODO: Does this actually happen?
					GlobalContext.endTransaction()
				}

				case HandleRequest(addr : Addr, request) =>	localObjects.get(addr) match {
					case None => sys.error(s"object $addr not found")
					case Some(obj) =>	sender() ! obj.handleRequest(request)
				}

				case CloseHandler =>
					context.stop(self)
			}
		}
	}
}

object AkkaReplicaSystem {

	private final val replicaActorName : String = "replica-base"

	sealed trait ReplicaActorMessage
	case class CreateObjectReplica[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyLevel : ConsistencyLevel, masterRef : ActorRef) extends ReplicaActorMessage {
		require(obj.isInstanceOf[Serializable])
	}
	case object AcquireHandler extends ReplicaActorMessage



	private[actors] class RefImpl[Addr, T <: AnyRef](val addr : Addr, val consistencyLevel : ConsistencyLevel, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T] {

		override implicit def toReplicatedObject : ReplicatedObject[T] = replicaSystem match {
			case null => sys.error(s"replica system has not been initialized properly. $toString")

			case akkaReplicaSystem: AkkaReplicaSystem[Addr] =>

				val start = System.currentTimeMillis()

				akkaReplicaSystem.localObjects.get(addr) match {
					case None => //retry
						sys.error(s"the replicated object '$addr' with consistency level $consistencyLevel is not available on this host.")

					case Some(rob : ReplicatedObject[T]) =>
						//Check that consistency level of reference matches the referenced object
						assert(rob.consistencyLevel == consistencyLevel, s"non-matching consistency levels. ref was $consistencyLevel and object was ${rob.consistencyLevel}")
						return rob
				}




		}

		override def toString : String = s"RefImpl($addr, $consistencyLevel)"
	}


}









