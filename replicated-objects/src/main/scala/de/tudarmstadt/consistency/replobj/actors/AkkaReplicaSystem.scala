package de.tudarmstadt.consistency.replobj.actors

import java.util.Random

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, ExtendedActorSystem, Props, RootActorPath}
import com.typesafe.config.{Config, ConfigFactory}
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem.{RefImpl, NewObjectJ}
import de.tudarmstadt.consistency.replobj.actors.StrongAkkaReplicatedObject.{StrongAkkaFollowerReplicatedObject, StrongAkkaMasterReplicatedObject}
import de.tudarmstadt.consistency.replobj.actors.WeakAkkaReplicatedObject.{WeakAkkaFollowerReplicatedObject, WeakAkkaMasterReplicatedObject}
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref, ReplicaSystem, ReplicatedObject, Utils}

import scala.collection.immutable.Stack
import scala.collection.mutable
import scala.concurrent.Await
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem[Addr] extends ReplicaSystem[Addr] {

  def actorSystem : ActorSystem

	private val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	ActorReplicaSystem.replicaActorName)

	/*private[actors]*/ val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	/*private[actors]*/ val localObjects : mutable.Map[Addr, AkkaReplicatedObject[ _, _]] = scala.collection.concurrent.TrieMap.empty



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

		val rob = createMasterReplicatedObject[T, L](obj, addr)

		println(s"created master actor at ${rob.objActor.path}")

		val ccls = typeTag[L].mirror.runtimeClass(typeTag[L].tpe)

		otherReplicas.foreach { actorRef =>
//			val msg = NewObject(addr, obj, null /*typeTag[T]*/, null /*typeTag[L]*/, rob.objActor)
			val msg = NewObjectJ(addr, obj, ccls, rob.objActor)
			actorRef ! msg
		}
		localObjects.put(addr, rob)

		RefImpl.create(addr, this)
	}

	override def ref[T  <: AnyRef : TypeTag,	L : TypeTag](addr : Addr) : Ref[Addr, T, L] = {
		RefImpl.create(addr, this)
	}


	private def createMasterReplicatedObject[T <: AnyRef : TypeTag, L : TypeTag](obj : T, addr : Addr) : AkkaReplicatedObject[T, L] = {

		val ref : AkkaReplicatedObject[T, _] =
			if (ConsistencyLevels.isWeak[L])
				new WeakAkkaMasterReplicatedObject[T](obj, this)
			else if (ConsistencyLevels.isStrong[L])
				new StrongAkkaMasterReplicatedObject[T](obj, this)
			else
				sys.error("unknown consistency")

		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
	}


	private def createFollowerReplicatedObject[T <: AnyRef : TypeTag, L : TypeTag](obj : T, addr : Addr, masterRef : ActorRef) : AkkaReplicatedObject[T, L] = {

		val ref : AkkaReplicatedObject[T, _] =
			if (ConsistencyLevels.isWeak[L])
				new WeakAkkaFollowerReplicatedObject[T](obj, masterRef, this)
			else if (ConsistencyLevels.isStrong[L])
				new StrongAkkaFollowerReplicatedObject[T](obj, masterRef, this)
			else
				sys.error("unknown consistency")

		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
	}



	private[actors] def initializeRefFields(obj : AnyRef) : Unit = {
		//TODO: Is this possible with scala reflection?
		obj.getClass.getDeclaredFields.foreach { field =>

			val ft = field.getType

			if (ft.isAssignableFrom(classOf[RefImpl[_,_,_]])) {
				field.setAccessible(true)
				val ref = field.get(obj)

				ref match {
					case akkaRef : RefImpl[Addr, _, _] =>
						akkaRef.replicaSystem = ActorReplicaSystem.this
					case _ =>
				}

				field.setAccessible(false)
			}

			//TODO: Check recursively for ref fields. Care for cycles (fields of type of the class the declares it)
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
		val sysname = ActorReplicaSystem.defaultActorSystemName
		val address = Address("akka.tcp", sysname, hostname, port)
		addOtherReplica(address)
	}

	def addOtherReplica(address : Address) : Unit = {
		/*
		Paths of actors are: akka.<protocol>://<actor system>@<hostname>:<port>/<actor path>
		Example: akka.tcp://actorSystemName@10.0.0.1:2552/user/actorName
		 */
		addOtherReplica(RootActorPath(address) / "user" / ActorReplicaSystem.replicaActorName)
	}


	private class ReplicaActor extends Actor {

		override def receive : Receive = {
//			case NewObject(addr : Addr, obj, objtype, consistency, masterRef) =>
//				/*Initialize a new replicated object on this host*/
//
//				//Ensure that no object already exists under this name
//				require(!localObjects.contains(addr))
//
//				//Set the replica system of all refs
//				initializeRefFields(obj)
//
//				//Create the replicated object on this replica and add it to the object map
//				val ref = createFollowerReplicatedObject(obj, addr, masterRef)(objtype, consistency)
//				localObjects.put(addr, ref)
			case NewObjectJ(addr : Addr, obj, consistencyCls, masterRef) =>
				/*Initialize a new replicated object on this host*/

				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr))

				//Set the replica system of all refs
				initializeRefFields(obj)

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplicatedObject(obj, addr, masterRef)(
					Utils.typeTagFromCls(obj.asInstanceOf[AnyRef].getClass.asInstanceOf[Class[AnyRef]]),
					Utils.typeTagFromCls(consistencyCls)
				)
				localObjects.put(addr, ref)
		}
	}
}

object AkkaReplicaSystem {

	private[AkkaReplicaSystem] final val replicaActorName : String = "replica-base"
	private[AkkaReplicaSystem] final val defaultActorSystemName : String = "replica-system"


	private class AkkaReplicaSystemImpl[Addr](override val actorSystem: ActorSystem) extends ActorReplicaSystem[Addr]


	def create[Addr](actorSystem : ActorSystem) : ActorReplicaSystem[Addr] =
		new AkkaReplicaSystemImpl[Addr](actorSystem)

	def create[Addr](port : Int) : ActorReplicaSystem[Addr] = {
		val config : Config = ConfigFactory.parseString(
			s"""
				|akka {
				| actor.provider = "remote"
				| remote {
				|   netty.tcp {
				|     hostname = "127.0.0.1"
				|     port = $port
				|   }
				| }
				|}
			""".stripMargin)

		val system = ActorSystem(defaultActorSystemName, config)

		println(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

		new AkkaReplicaSystemImpl[Addr](system)
	}


	class AkkaRef[Addr, T <: AnyRef, L : TypeTag] private (val addr : Addr, @transient private[actors] var replicaSystem : ActorReplicaSystem[Addr]) extends Ref[Addr, T, L] {

		override implicit def toReplicatedObject : ReplicatedObject[T, L] = replicaSystem match {
			case null =>
				sys.error(s"replica system has not been initialized properly. $toString")
			case akkaReplicaSystem: ActorReplicaSystem[Addr] => akkaReplicaSystem.localObjects.get(addr) match {
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
			s"AkkaRef($addr)"
	}

	object AkkaRef {

		def create[Addr, T <: AnyRef, L : TypeTag](addr : Addr, replicaSystem : ActorReplicaSystem[Addr]) : AkkaRef[Addr, T, L] = {
			new AkkaRef[Addr, T, L](addr, replicaSystem)
		}

		/* Java binding */
		def create[Addr, T <: AnyRef, L](addr : Addr, replicaSystem: ActorReplicaSystem[Addr], consistencyCls : Class[L]) : AkkaRef[Addr, T, L] = {
			implicit val ltt : TypeTag[L] = Utils.typeTagFromCls(consistencyCls)
			val ref : AkkaRef[Addr, T, L] = create[Addr, T, L](addr, replicaSystem)
			ref
		}
	}

	trait ReplicaActorMessage
//	case class NewObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, objtype : TypeTag[T], consistency : TypeTag[L], masterRef : ActorRef) extends ReplicaActorMessage
	/*TODO: The case class above is the preferred way to handle it, but our self made type tags (that are used for the Java integration) are not serializable.*/
	case class NewObjectJ[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyCls : Class[L], masterRef : ActorRef) extends ReplicaActorMessage
}









