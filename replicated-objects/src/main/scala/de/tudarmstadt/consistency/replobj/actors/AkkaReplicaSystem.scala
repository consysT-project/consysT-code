package de.tudarmstadt.consistency.replobj.actors

import java.util.Random

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, Props, RootActorPath}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem.{NewObjectJ, ObjReq, Ref, Request}
import de.tudarmstadt.consistency.replobj.{Ref, ReplicaSystem, ReplicatedObject, Utils}

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._

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


	private [actors] object Context {

		final type CtxType = Int
		final type ContextPath = List[CtxType]

		private var currentContextPath : ContextPath = List.empty[CtxType]

		private val random = new Random()


		def createCtxType() : Int = random.nextInt()

		def enterCtx(ctx : CtxType = createCtxType()) : Unit =
			currentContextPath = ctx :: currentContextPath

		def leaveCtx() : Unit =
			currentContextPath = currentContextPath.tail

		def getCurrentContext : ContextPath = currentContextPath
	}



	override def replicate[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : Ref[Addr, T, L] = {
		require(!localObjects.contains(addr))

		val rob = createMasterReplica[T, L](addr, obj)

		val ccls = typeTag[L].mirror.runtimeClass(typeTag[L].tpe)

		otherReplicas.foreach { actorRef =>
			val msg = NewObjectJ(addr, obj, ccls, replicaActor)
			actorRef ! msg
		}
		localObjects.put(addr, rob)

		Ref.create(addr, this)
	}

	override def ref[T  <: AnyRef : TypeTag,	L : TypeTag](addr : Addr) : Ref[Addr, T, L] = {
		Ref.create(addr, this)
	}


	protected def createMasterReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T, L] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T, L] =
		sys.error("unknown consistency")

//	private def createMasterReplicatedObject[T <: AnyRef : TypeTag, L : TypeTag](obj : T, addr : Addr) : AkkaReplicatedObject[T, L] = {
//
//		val ref : AkkaReplicatedObject[T, _] =
//			if (ConsistencyLevels.isWeak[L])
//				new WeakAkkaMasterReplicatedObject[T](obj, this)
//			else if (ConsistencyLevels.isStrong[L])
//				new StrongAkkaMasterReplicatedObject[T](obj, this)
//			else
//				sys.error("unknown consistency")
//
//		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
//	}
//
//
//	private def createFollowerReplicatedObject[T <: AnyRef : TypeTag, L : TypeTag](obj : T, addr : Addr, masterRef : ActorRef) : AkkaReplicatedObject[T, L] = {
//
//		val ref : AkkaReplicatedObject[T, _] =
//			if (ConsistencyLevels.isWeak[L])
//				new WeakAkkaFollowerReplicatedObject[T](obj, masterRef, this)
//			else if (ConsistencyLevels.isStrong[L])
//				new StrongAkkaFollowerReplicatedObject[T](obj, masterRef, this)
//			else
//				sys.error("unknown consistency")
//
//		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
//	}

	private[actors] final def request(addr : Addr, req : Request, replicaRef : ActorRef = replicaActor, receiveTimeout : FiniteDuration = 10 seconds) : Any = {
		val reqMsg = ObjReq(addr, req)

		if (req.returns) {
			import akka.pattern.ask
			val response = replicaRef.ask(reqMsg)(Timeout(receiveTimeout))
			val result = Await.result(response, receiveTimeout)
			result
		} else {
			replicaRef ! reqMsg
		}
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
			case NewObjectJ(addr : Addr, obj, consistencyCls, masterRef) =>
				/*Initialize a new replicated object on this host*/

				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr))

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplica(addr, obj, masterRef)(
					Utils.typeTagFromCls(obj.asInstanceOf[AnyRef].getClass.asInstanceOf[Class[AnyRef]]),
					Utils.typeTagFromCls(consistencyCls)
				)
				localObjects.put(addr, ref)

			case ObjReq(addr : Addr, request) => localObjects.get(addr) match {
				case None => sys.error("object not found, address: " + addr)
				case Some(rob) => rob.objActor.tell(request, sender())
			}
		}
	}
}

object AkkaReplicaSystem {

	private final val replicaActorName : String = "replica-base"


	trait Request {	def returns : Boolean }
	trait ReturnRequest { self : Request =>	override def returns : Boolean = true }
	trait NonReturnRequest { self : Request => override def returns : Boolean = false}


	trait ReplicaActorMessage
	//	case class NewObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, objtype : TypeTag[T], consistency : TypeTag[L], masterRef : ActorRef) extends ReplicaActorMessage
	/*TODO: The case class above is the preferred way to handle it, but our self made type tags (that are used for the Java integration) are not serializable.*/
	case class NewObjectJ[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyCls : Class[L], masterRef : ActorRef) extends ReplicaActorMessage
	case class ObjReq[Addr](addr : Addr, request : Request) extends ReplicaActorMessage




	private[actors] class RefImpl[Addr, T <: AnyRef, L : TypeTag](val addr : Addr, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T, L] {
		override implicit def toReplicatedObject : ReplicatedObject[T, L] = replicaSystem match {
			case null =>
				sys.error(s"replica system has not been initialized properly. $toString")
			case akkaReplicaSystem: AkkaReplicaSystem[Addr] => akkaReplicaSystem.localObjects.get(addr) match {
				case None =>
					sys.error("the replicated object is not (yet) available on this host.")

				case Some(rob : ReplicatedObject[T,L]) =>

					//Check consistency level
					val thisL = implicitly[TypeTag[L]].tpe
					val objL = rob.getConsistencyLevel.tpe
					require(thisL =:= objL, s"non-matching consistency levels. ref was $thisL and object was $objL")

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









