package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.{Ref, ReplicaSystem}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystem[Addr] extends ReplicaSystem[Addr] {

	def actorSystem : ActorSystem

	def name : String

	val replicaActor : ActorRef =
		actorSystem.actorOf(
			Props(
				classOf[ReplicaActor[Addr]],
				this),
			name)

	private[actors] val otherReplicas : mutable.Set[ActorRef] = mutable.Set.empty

	private[actors] val localObjects : mutable.Map[Addr, AkkaRef[Addr, _, _]] = scala.collection.concurrent.TrieMap.empty


	override def replicate[T : TypeTag, L : TypeTag](addr : Addr, obj : T) : Ref[T, L] = {
		require(!localObjects.contains(addr))

		val ref = createMasterRef[T, L](obj, addr)

		otherReplicas.foreach(actorRef => actorRef ! NewObject(addr, ref.objActor, obj, typeTag[T], typeTag[Weak]))
		localObjects.put(addr, ref)

		ref
	}

	def createMasterRef[T : TypeTag, L : TypeTag](obj : T, addr : Addr) : AkkaRef[Addr, T, L] = {
		val ref : AkkaRef[Addr, T, _] = if (typeTag[L] == typeTag[Weak])
			new WeakAkkaMasterRef[Addr, T](obj, this, addr)
		else if (typeTag[L] == typeTag[Strong])
			new WeakAkkaMasterRef[Addr, T](obj, this, addr)
		else
			sys.error("unknown consistency")

		ref.asInstanceOf[AkkaRef[Addr, T, L]] //<- L has to be the consistency level ref
	}





	override def ref[T : TypeTag,	L : TypeTag](addr : Addr) : Ref[T, L] =
		localObjects(addr).asInstanceOf[Ref[T, L]]



	def addOtherReplica(replicaActorRef : ActorRef) : Unit =
		otherReplicas.add(replicaActorRef)




}



class ReplicaActor[Addr](val replica : AkkaReplicaSystem[Addr]) extends Actor {

	override def receive : Receive = {
		case NewObject(addr : Addr, masterRef, obj, objtype, consistency) =>
			require(!replica.localObjects.contains(addr))

			val ref = createFollowerRef(obj, addr, masterRef)(objtype, consistency)
			replica.localObjects.put(addr, ref)
	}


	def createFollowerRef[T : TypeTag, L : TypeTag](obj : T, addr : Addr, masterRef : ActorRef) : AkkaRef[Addr, T, L] = {
		val ref : AkkaRef[Addr, T, _] = if (typeTag[L] == typeTag[Weak])
			new WeakAkkaFollowerRef[Addr, T](obj, masterRef, replica, addr)
		else if (typeTag[L] == typeTag[Strong])
			new WeakAkkaFollowerRef[Addr, T](obj, masterRef, replica, addr)
		else
			sys.error("unknown consistency")

		ref.asInstanceOf[AkkaRef[Addr, T, L]] //<- L has to be the consistency level ref
	}
}



trait ReplicaActorMessage
case class NewObject[Addr, T, L](addr : Addr, masterRef : ActorRef, obj : Any, objtype : TypeTag[T], consistency : TypeTag[L]) extends ReplicaActorMessage



