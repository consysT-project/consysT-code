package de.tudarmstadt.consistency.replobj.actors

import java.util.Random

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Address, ExtendedActorSystem, Props, RootActorPath}
import akka.util.Timeout
import com.typesafe.config.{Config, ConfigFactory}
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem._
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref, ReplicaSystem, ReplicatedObject, Utils, typeToClassTag}

import scala.collection.immutable.Stack
import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

import scala.concurrent.duration._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait ActorReplicaSystem[Addr] extends ReplicaSystem[Addr] {

	def actorSystem : ActorSystem

	private val replicaActor : ActorRef = actorSystem.actorOf(Props(classOf[ReplicaActor], this),	ActorReplicaSystem.replicaActorName)

	private val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	private val localObjects : mutable.Map[Addr, ActorReplicatedObject[ _, _]] = scala.collection.concurrent.TrieMap.empty



	private [single] object Context {

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

		println(s"created master actor for object <$addr> at ${replicaActor.path}")

		val ccls = typeTag[L].mirror.runtimeClass(typeTag[L].tpe)

		otherReplicas.foreach { actorRef =>
			//			val msg = NewObject(addr, obj, null /*typeTag[T]*/, null /*typeTag[L]*/, rob.objActor)
			val msg = JNewReplicatedObject(addr, obj, ccls, replicaActor)
			actorRef ! msg
		}
		localObjects.put(addr, rob)

		RefImpl.create(addr, this)
	}

	override def ref[T  <: AnyRef : TypeTag,	L : TypeTag](addr : Addr) : Ref[Addr, T, L] = {
		RefImpl.create(addr, this)
	}

	protected def createMasterReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : ActorReplicatedObject[T, L] =
		sys.error("unknown consistency")

	protected def createFollowerReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T, masterRef : ActorRef) : ActorReplicatedObject[T, L] =
		sys.error("unknown consistency")


	final def request(addr : Addr, request : Request, receiveTimeout : FiniteDuration = 10 seconds) : Option[Any] = {
		request(replicaActor, addr, request, receiveTimeout)
	}

	final def request(replicaRef : ActorRef, addr : Addr, request : Request, receiveTimeout : FiniteDuration = 10 seconds) : Option[Any] = {
		val reqMsg = ObjReq(addr, request)

		if (request.returns) {
			import akka.pattern.ask
			val response = replicaRef.ask(reqMsg)(Timeout(receiveTimeout))
			val result = Await.result(response, receiveTimeout)
			Some(result)
		} else {
			replicaRef ! reqMsg
			None
		}
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
			case JNewReplicatedObject(addr : Addr, obj, consistencyCls, masterRef) =>
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
				case Some(rob) => rob.synchronized {
					rob.handleRequest(request.asInstanceOf[rob.Req]) match {
						case None =>
						case Some(ret) => sender() ! ret
					}
				}
			}
		}
	}




	trait ActorReplicatedObject[T <: AnyRef, L] extends ReplicatedObject[T, L] {

		val addr : Addr
		private var obj : T = null.asInstanceOf[T]

		protected implicit def ttt : TypeTag[T]
		protected implicit def ltt : TypeTag[L]


		protected object ReflectiveAccess {

			private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument

			//TODO: Define this as field and keep in sync with obj
			@inline private def objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)

			def doInvoke[R](methodName : String, args : Any*) : R = synchronized {
				val methodSymbol = typeOf[T].decl(TermName(methodName)).asMethod
				val methodMirror = objMirror.reflectMethod(methodSymbol)
				val result = methodMirror.apply(args : _*)
				result.asInstanceOf[R]
			}

			def doGetField[R](fieldName : String) : R = synchronized {
				val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
				val fieldMirror = objMirror.reflectField(fieldSymbol)
				val result = fieldMirror.get
				result.asInstanceOf[R]
			}

			def doSetField[R](fieldName : String, value : R) : Unit = synchronized {
				val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
				val fieldMirror = objMirror.reflectField(fieldSymbol)
				fieldMirror.set(value).asInstanceOf[R]
			}
		}


		protected def setObject(newObj : T) : Unit = {
			obj = newObj
			initializeRefFields()
			//objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)
		}

		protected def getObject : T = obj


		private def initializeRefFields() : Unit = {
			//TODO: Is this possible with scala reflection?
			obj.getClass.getDeclaredFields.foreach { field =>
				if (field.getType.isAssignableFrom(classOf[RefImpl[_,_,_]])) {
					field.setAccessible(true)
					field.get(obj) match {
						case refImpl : RefImpl[Addr, _, _] =>
							refImpl.replicaSystem = ActorReplicaSystem.this
						case _ =>
					}
				}
				//TODO: Check recursively for ref fields. Care for cycles (fields of type of the class the declares it)
			}
		}

		type Req <: Request
		def handleRequest(request : Req) : Option[Any]


		override def print() : Unit = ???


		override def getConsistencyLevel : TypeTag[L] =
			implicitly[TypeTag[L]]

	}
}

object ActorReplicaSystem {

	private[ActorReplicaSystem] final val replicaActorName : String = "replica-base"
	private[ActorReplicaSystem] final val defaultActorSystemName : String = "replica-system"


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


	class RefImpl[Addr, T <: AnyRef, L : TypeTag] private(val addr : Addr, @transient private[single] var replicaSystem : ActorReplicaSystem[Addr]) extends Ref[Addr, T, L] {

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

	object RefImpl {

		def create[Addr, T <: AnyRef, L : TypeTag](addr : Addr, replicaSystem : ActorReplicaSystem[Addr]) : Ref[Addr, T, L] = {
			new RefImpl[Addr, T, L](addr, replicaSystem)
		}

		/* Java binding */
		def create[Addr, T <: AnyRef, L](addr : Addr, replicaSystem: ActorReplicaSystem[Addr], consistencyCls : Class[L]) : Ref[Addr, T, L] = {
			implicit val ltt : TypeTag[L] = Utils.typeTagFromCls(consistencyCls)
			val ref : Ref[Addr, T, L] = create[Addr, T, L](addr, replicaSystem)
			ref
		}
	}

	trait Request {
		def returns : Boolean
	}

	trait ReturnRequest extends Request {
		override final val returns = false
	}

	trait ReplicaActorMessage
	//This message uses class instead of typeTag to be compatible with Java
	case class NewObjectJ[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyCls : Class[L], masterRef : ActorRef) extends ReplicaActorMessage

	case class JNewReplicatedObject[Addr, T <: AnyRef, L](addr : Addr, obj : T, consistencyCls : Class[L], masterReplica : ActorRef) extends ReplicaActorMessage

	case class ObjReq[Addr, Return](addr : Addr, request : Request) extends ReplicaActorMessage
}









