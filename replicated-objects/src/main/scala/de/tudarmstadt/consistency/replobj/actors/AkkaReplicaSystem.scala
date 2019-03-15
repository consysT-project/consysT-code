package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, Props, RootActorPath}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.ContextPath.ContextPathBuilder
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

	private[actors] final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	AkkaReplicaSystem.replicaActorName)

	/*private[actors]*/ val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	/*private[actors]*/ val localObjects : mutable.Map[Addr, AkkaReplicatedObject[Addr, _]] = scala.collection.concurrent.TrieMap.empty


	private[actors] object GlobalContext {
		private var builder : DynamicVariable[Option[ContextPathBuilder]] = new DynamicVariable(None)

		private def setBuilder(builder: ContextPathBuilder) : Unit = {
			this.builder.value = Some(builder)
		}

		def resetBuilder() : Unit = {
			this.builder.value = None
		}

		def getBuilder : ContextPathBuilder = {
			require(hasBuilder)
			builder.value.get
		}

		def hasBuilder : Boolean =
			builder.value.nonEmpty


		def startNewTransaction() : Unit = {
			require(!hasBuilder)
			val txid = Random.nextInt
			setBuilder(new ContextPathBuilder(txid))
		}

		def endTransaction() : Unit = {
			require(hasBuilder)
			resetBuilder()
		}

		def setContext(path : ContextPath) : Unit = {
			require(builder.value.isEmpty)
			setBuilder(new ContextPathBuilder(path))
		}

		override def toString : String = s"context($builder)"

	}


	protected def freshAddr() : Addr


	override final def replicate[T <: AnyRef : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[Addr, T] = {
		require(!localObjects.contains(addr))
		log(s"replicating object $addr := $obj")

		val rob = createMasterReplica[T](l, addr, obj)

		otherReplicas.foreach(actorRef =>	actorRef ! CreateObjectReplica(addr, obj, l, replicaActor))
		localObjects.put(addr, rob)

		Ref.create(addr, l, this)
	}


	override final def replicate[T <: AnyRef : TypeTag](obj : T, l : ConsistencyLevel) : Ref[Addr, T] = {
		replicate[T](freshAddr(), obj, l)
	}

	override final def ref[T <: AnyRef : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[Addr, T] = {
		Ref.create(addr, l, this)
	}


	protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] =
		sys.error("unknown consistency")




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

		println(s"selecting actor: $replicaActorPath")
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


	private[actors] def initializeRefFieldsFor(obj : Any) : Unit = {

		val alreadyVisited : mutable.Set[Any] = mutable.Set.empty

		def initializeObject(any : Any) : Unit = {
			if (any == null) {
				return
			}

			any match {
				//If the object is a RefImpl
				case refImpl : RefImpl[Addr, _, _] =>
					refImpl.replicaSystem = this

				case ref : Ref[Addr, _] =>
					sys.error(s"cannot initialize unknown implementation of Ref. $ref : ${ref.getClass}")

				case _ =>

					val anyClass = any.getClass
					//If the value is not an object class then stop TODO: Initialize arrays
					if (anyClass.isPrimitive || anyClass.isArray) {
						return
					}

					val anyPackage = anyClass.getPackage
					//Check that the object has a package declaration and that it is not the Java standard library
					if (anyPackage == null || anyPackage.getImplementationTitle == "Java Runtime Environment") {
						return
					}

					//If the object should be initialized, then initialize all fields
					any.getClass.getDeclaredFields.foreach { field =>
						//Field is an object => recursively initialize refs in that object
						field.setAccessible(true)
						val fieldObj = field.get(any)
						if (!alreadyVisited.contains(fieldObj)) initializeObject(fieldObj)
					}
			}
		}


		initializeObject(obj)
	}



	def acquireHandlerFrom(replicaRef : ActorRef, receiveTimeout : FiniteDuration = 30 seconds) : RequestHandler[Addr] = {
		import akka.pattern.ask
		val response = replicaRef.ask(AcquireHandler)(Timeout(receiveTimeout))
		val result = Await.result(response, receiveTimeout)
		result.asInstanceOf[RequestHandler[Addr]]
	}


	private class ReplicaActor extends Actor {


		override def receive : Receive = {

			case Debug(x) =>
				println(s"Debug $x from ${sender()}")

			case CreateObjectReplica(addr : Addr, obj, consistencyLevel, masterRef) =>
				/*Initialize a new replicated object on this host*/
				log(s"received object $addr := $obj")

				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr))

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplica(consistencyLevel, addr, obj, masterRef)(
					Utils.typeTagFromCls(obj.asInstanceOf[AnyRef].getClass.asInstanceOf[Class[AnyRef]])
				)
				localObjects.put(addr, ref)


			case msg@HandleRemoteRequest(addr : Addr, request) =>
				log(s"received remote request for object $addr: $request")

				val handlerRef = context.actorOf(Props(classOf[RequestHandlerActor], this))
				handlerRef.tell(HandleRequest(addr, request), sender())

			case AcquireHandler =>
				val handler = new RequestHandlerImpl(
					context.actorOf(
						Props(classOf[RequestHandlerActor], this)
							.withDispatcher("request-dispatcher")
					)
				)
				sender() ! handler
		}


		private class RequestHandlerActor extends Actor {

			override def receive : Receive = {
				case InitHandler =>
					GlobalContext.resetBuilder()

				case HandleRequest(addr : Addr, request) =>
					localObjects.get(addr) match {
						case None =>
							sys.error(s"object $addr not found")
						case Some(obj) =>
							sender() ! obj.handleRequest(request)
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
	//	case class NewObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, objtype : TypeTag[T], consistency : TypeTag[L], masterRef : ActorRef) extends ReplicaActorMessage
	/*TODO: The case class above is the preferred way to handle it, but our self made type tags (that are used for the Java integration) are not serializable.*/
	case class CreateObjectReplica[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyLevel : ConsistencyLevel, masterRef : ActorRef) extends ReplicaActorMessage
//	case class HandleLocalRequest[Addr](addr : Addr, request : Request) extends ReplicaActorMessage
	case class HandleRemoteRequest[Addr](addr : Addr, request : Request) extends ReplicaActorMessage

	case object AcquireHandler extends ReplicaActorMessage

	case class Debug(any : Any) extends ReplicaActorMessage






	private[actors] class RefImpl[Addr, T <: AnyRef, L](val addr : Addr, val consistencyLevel : ConsistencyLevel, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T] {
		override implicit def toReplicatedObject : ReplicatedObject[T] = replicaSystem match {
			case null =>
				sys.error(s"replica system has not been initialized properly. $toString")
			case akkaReplicaSystem: AkkaReplicaSystem[Addr] => akkaReplicaSystem.localObjects.get(addr) match {
				case None =>
					sys.error("the replicated object is not (yet) available on this host.")

				case Some(rob : ReplicatedObject[T]) =>

					//Check consistency level
//					val thisL = implicitly[TypeTag[L]].tpe
//					val objL = rob.getConsistencyLevel.tpe
//					require(thisL =:= objL, s"non-matching consistency levels. ref was $thisL and object was $objL")

					rob
			}
		}

		override def toString : String = s"RefImpl($addr, $consistencyLevel)"
	}

	private object Ref {

		def create[Addr, T <: AnyRef, L](addr : Addr, consistencyLevel : ConsistencyLevel, replicaSystem : AkkaReplicaSystem[Addr]) : RefImpl[Addr, T, L] = {
			new RefImpl[Addr, T, L](addr, consistencyLevel, replicaSystem)
		}

//		/* Java binding */
//		def create[Addr, T <: AnyRef, L](addr : Addr, replicaSystem: AkkaReplicaSystem[Addr], consistencyCls : Class[L]) : RefImpl[Addr, T, L] = {
//			implicit val ltt : TypeTag[L] = Utils.typeTagFromCls(consistencyCls)
//			val ref : RefImpl[Addr, T, L] = create[Addr, T, L](addr, replicaSystem)
//			ref
//		}
	}
}









