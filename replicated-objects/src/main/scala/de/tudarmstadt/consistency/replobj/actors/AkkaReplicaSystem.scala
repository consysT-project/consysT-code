package de.tudarmstadt.consistency.replobj.actors

import java.lang.reflect.Field

import akka.actor.{Actor, ActorPath, ActorRef, ActorSystem, Props}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.actors.WeakAkkaReplicatedObject.{WeakAkkaFollowerReplicatedObject, WeakAkkaMasterReplicatedObject}
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref, ReplicaSystem, ReplicatedObject, typeToClassTag}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem[Addr] extends ReplicaSystem[Addr] {

  def actorSystem : ActorSystem

	def name : String

	private val replicaActor : ActorRef =
		actorSystem.actorOf(
			Props(
				classOf[ReplicaActor],
				this),
			name)


	/*private[actors]*/ val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	/*private[actors]*/ val localObjects : mutable.Map[Addr, AkkaReplicatedObject[ _, _]] = scala.collection.concurrent.TrieMap.empty


	override def replicate[T : TypeTag, L : TypeTag](addr : Addr, obj : T) : Ref[Addr, T, L] = {
		require(!localObjects.contains(addr))

		val rob = createMasterReplicatedObject[T, L](obj, addr)

		otherReplicas.foreach { actorRef =>
			val msg = NewObject(addr, obj, typeTag[T], typeTag[Weak], rob.objActor)
			actorRef ! msg
		}
		localObjects.put(addr, rob)

		new AkkaRef(addr, this)
	}

	def createMasterReplicatedObject[T : TypeTag, L : TypeTag](obj : T, addr : Addr) : AkkaReplicatedObject[T, L] = {

		val ref : AkkaReplicatedObject[T, _] =
			if (ConsistencyLevels.isWeak[L])
				new WeakAkkaMasterReplicatedObject[Addr, T](obj, actorSystem)
			else if (ConsistencyLevels.isStrong[L])
				???
			else
				sys.error("unknown consistency")

		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
	}


	def createFollowerReplicatedObject[T : TypeTag, L : TypeTag](obj : T, addr : Addr, masterRef : ActorRef) : AkkaReplicatedObject[T, L] = {

		val ref : AkkaReplicatedObject[T, _] =
			if (ConsistencyLevels.isWeak[L])
				new WeakAkkaFollowerReplicatedObject[Addr, T](obj, masterRef, actorSystem)
			else if (ConsistencyLevels.isStrong[L])
				???
			else
				sys.error("unknown consistency")

		ref.asInstanceOf[AkkaReplicatedObject[T, L]] //<- L has to be the consistency level ref
	}




	override def ref[T : TypeTag,	L : TypeTag](addr : Addr) : Ref[Addr, T, L] = {
		require(localObjects.contains(addr))
		new AkkaRef(addr, this)
	}


	def addOtherReplica(replicaActorRef : ActorRef) : Unit =
		otherReplicas.add(replicaActorRef)



	class ReplicaActor extends Actor {

		override def receive : Receive = {
			case NewObject(addr : Addr, obj, objtype, consistency, masterRef) =>
				/*Initialize a new replicated object on this host*/

				//Ensure that no object already exists under this name
				require(!localObjects.contains(addr))

				//Set the replica system of all refs
				setReplicaSystemOfFields(obj.asInstanceOf[AnyRef])

				//Create the replicated object on this replica and add it to the object map
				val ref = createFollowerReplicatedObject(obj, addr, masterRef)(objtype, consistency)
				localObjects.put(addr, ref)
		}


		private def setReplicaSystemOfFields(obj : AnyRef) : Unit = {
			//TODO: Is this possible with scala reflection?
			obj.getClass.getDeclaredFields.foreach { field =>

				val ft = field.getType

				if (ft.isAssignableFrom(classOf[AkkaRef[_,_,_]])) {
					field.setAccessible(true)
					val ref = field.get(obj)

					ref match {
						case akkaRef : AkkaRef[Addr, _, _] =>
							akkaRef.replicaSystem = AkkaReplicaSystem.this
						case _ =>
					}

					field.setAccessible(false)
				}

				//TODO: CHeck recursively for ref fields
			}
		}
	}
}

object AkkaReplicaSystem {

	private class AkkaReplicaSystemImpl[Addr](val actorSystem: ActorSystem, val name : String) extends AkkaReplicaSystem[Addr]

	def create[Addr](actorSystem : ActorSystem, name : String) : AkkaReplicaSystem[Addr] =
		new AkkaReplicaSystemImpl[Addr](actorSystem, name)
}

class AkkaRef[Addr, T, L](val addr : Addr, @transient private[actors] var replicaSystem : AkkaReplicaSystem[Addr]) extends Ref[Addr, T, L] {

	override implicit def toReplicatedObject : ReplicatedObject[T, L] = replicaSystem match {
		case null =>
			sys.error(s"replica system has not been initialized properly")
		case akkaReplicaSystem: AkkaReplicaSystem[Addr] =>
			akkaReplicaSystem.localObjects(addr).asInstanceOf[ReplicatedObject[T, L]]
	}

}



trait ReplicaActorMessage
case class NewObject[Addr, T, L](addr : Addr, obj : Any, objtype : TypeTag[T], consistency : TypeTag[L], masterRef : ActorRef) extends ReplicaActorMessage



