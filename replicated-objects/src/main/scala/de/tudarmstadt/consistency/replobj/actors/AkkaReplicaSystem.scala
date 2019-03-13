package de.tudarmstadt.consistency.replobj.actors

import java.util.function.Supplier

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, Props, RootActorPath}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.Requests.{LocalReq, Request}
import de.tudarmstadt.consistency.replobj.{Ref, ReplicaSystem, ReplicatedObject, Utils}

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.Random

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem[Addr] extends ReplicaSystem[Addr] {

  def actorSystem : ActorSystem

	private[actors] final val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	AkkaReplicaSystem.replicaActorName)

	/*private[actors]*/ val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	/*private[actors]*/ val localObjects : mutable.Map[Addr, AkkaReplicatedObject[Addr, _, _]] = scala.collection.concurrent.TrieMap.empty


	private[actors] object context {
		private var currentPath : Option[ContextPath] = None

		def newTransaction() : Unit = {
			require(currentPath.isEmpty)
			currentPath = Some(ContextPath.create(Random.nextInt))
			setPath(_.push())
		}



		def endTransaction() : Unit = {
			require(currentPath.nonEmpty)
			setPath(_.pop())
			require(currentPath.get.isEmpty)
			currentPath = None
		}

		def isEmpty : Boolean = currentPath.isEmpty

		def getPath : ContextPath = {
			require(currentPath.nonEmpty)
			currentPath.get
		}

		def setPath(transformer : ContextPath => ContextPath) : Unit = {
			require(currentPath.nonEmpty)
			currentPath = currentPath.map(transformer)
		}

	}


	protected def freshAddr() : Addr


	override final def replicate[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : Ref[Addr, T, L] = {
		require(!localObjects.contains(addr))

		log(s"replicating object $addr := $obj")

		val rob = createMasterReplica[T, L](addr, obj)
		val ccls = typeTag[L].mirror.runtimeClass(typeTag[L].tpe)

		otherReplicas.foreach { actorRef =>
			val msg = NewJObject(addr, obj, ccls, replicaActor)
			actorRef ! msg
		}
		localObjects.put(addr, rob)

		Ref.create(addr, this)
	}

	override final def replicate[T <: AnyRef : TypeTag, L : TypeTag](obj : T) : Ref[Addr, T, L] = {
		replicate[T, L](freshAddr(), obj)
	}

	override final def ref[T  <: AnyRef : TypeTag,	L : TypeTag](addr : Addr) : Ref[Addr, T, L] = {
		Ref.create(addr, this)
	}


	protected def createMasterReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T, L] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T, L] =
		sys.error("unknown consistency")


	private[actors] final def request(addr : Addr, req : Request, replicaRef : ActorRef = replicaActor, receiveTimeout : FiniteDuration = 3600 seconds) : Any = {
		val reqMsg = if (replicaRef.path == replicaActor.path)
			HandleLocalRequest(addr, req)
		else
			HandleRemoteRequest(addr, req)

		if (req.returns) {
			import akka.pattern.ask
			val response = replicaRef.ask(reqMsg)(Timeout(receiveTimeout))
			val result = Await.result(response, receiveTimeout)
			result
		} else {
			replicaRef ! reqMsg
		}
	}



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




	private class ReplicaActor extends Actor {
		override def receive : Receive = {

			case Debug(x) =>
				println(s"Debug $x from ${sender()}")

			case NewJObject(addr : Addr, obj, consistencyCls, masterRef) =>
				/*Initialize a new replicated object on this host*/
				log(s"received object $addr := $obj")

				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr))

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplica(addr, obj, masterRef)(
					Utils.typeTagFromCls(obj.asInstanceOf[AnyRef].getClass.asInstanceOf[Class[AnyRef]]),
					Utils.typeTagFromCls(consistencyCls)
				)
				localObjects.put(addr, ref)

			case HandleLocalRequest(addr : Addr, request) =>
				require(request.isInstanceOf[LocalReq], s"can only handle local requests on local replica, but got $request")

				log(s"received local request for object $addr: $request")
				localObjects.get(addr) match {
					case None => sys.error("object not found, address: " + addr)
					case Some(rob) =>
						rob.objActor.tell(request, sender())
				}

			case HandleRemoteRequest(addr : Addr, request) =>
				require(!request.isInstanceOf[LocalReq], s"can only handle non-local requests on remote replica, but got $request")

				log(s"received remote request for object $addr: $request")
				localObjects.get(addr) match {
					case None => sys.error("object not found, address: " + addr)
					case Some(rob) =>
						rob.objActor.tell(request, sender())
				}

		}
	}
}

object AkkaReplicaSystem {

	private final val replicaActorName : String = "replica-base"







	sealed trait ReplicaActorMessage
	//	case class NewObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, objtype : TypeTag[T], consistency : TypeTag[L], masterRef : ActorRef) extends ReplicaActorMessage
	/*TODO: The case class above is the preferred way to handle it, but our self made type tags (that are used for the Java integration) are not serializable.*/
	case class NewJObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyCls : Class[L], masterRef : ActorRef) extends ReplicaActorMessage
	case class HandleLocalRequest[Addr](addr : Addr, request : Request) extends ReplicaActorMessage
	case class HandleRemoteRequest[Addr](addr : Addr, request : Request) extends ReplicaActorMessage
	case class Debug(any : Any) extends ReplicaActorMessage





	private[actors] class RefImpl[Addr, T <: AnyRef, L : TypeTag](val addr : Addr, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T, L] {
		override implicit def toReplicatedObject : ReplicatedObject[T, L] = replicaSystem match {
			case null =>
				sys.error(s"replica system has not been initialized properly. $toString")
			case akkaReplicaSystem: AkkaReplicaSystem[Addr] => akkaReplicaSystem.localObjects.get(addr) match {
				case None =>
					sys.error("the replicated object is not (yet) available on this host.")

				case Some(rob : ReplicatedObject[T,L]) =>

					//Check consistency level
//					val thisL = implicitly[TypeTag[L]].tpe
//					val objL = rob.getConsistencyLevel.tpe
//					require(thisL =:= objL, s"non-matching consistency levels. ref was $thisL and object was $objL")

					rob
			}
		}

		override def toString : String =
			s"RefImpl($addr)"
	}

	private object Ref {

		def create[Addr, T <: AnyRef, L : TypeTag](addr : Addr, replicaSystem : AkkaReplicaSystem[Addr]) : RefImpl[Addr, T, L] = {
			new RefImpl[Addr, T, L](addr, replicaSystem)
		}

		/* Java binding */
		def create[Addr, T <: AnyRef, L](addr : Addr, replicaSystem: AkkaReplicaSystem[Addr], consistencyCls : Class[L]) : RefImpl[Addr, T, L] = {
			implicit val ltt : TypeTag[L] = Utils.typeTagFromCls(consistencyCls)
			val ref : RefImpl[Addr, T, L] = create[Addr, T, L](addr, replicaSystem)
			ref
		}
	}
}









