package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorPath, ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.DistributedStore
import de.tudarmstadt.consistency.replobj.actors.ObjActor._

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
class ActorStore(implicit val actorSystem : ActorSystem) extends DistributedStore[String, ActorPath] {
	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using the specified address.
		*
		* @param addr  The (distributed) address of the object
		* @param value The object to distribute
		* @return A reference to the created object
		*/
	override def distribute[T : TypeTag, L : TypeTag](addr : String, value : T) : Ref[T, L] = {
		val ltt = implicitly[TypeTag[L]]

		if (ltt == typeTag[ConsistencyLevels.Inconsistent]) {
			val actorRef = actorSystem.actorOf(Props(classOf[InconsistentActors.LeaderActor[T]], value, typeTag[T]), addr)
			new ObjRef[T, L](actorRef)
		} else if (ltt == typeTag[ConsistencyLevels.Weak]) {
			val actorRef = actorSystem.actorOf(Props(classOf[WeakActors.LeaderActor[T]], value, typeTag[T]), addr)
			new ObjRef[T, L](actorRef)
		} else {
			throw new UnsupportedOperationException("unknown consistency level: " + ltt)
		}


	}


	//TODO: replicate can return even though the state replication has not finished yet. Thus it can include "future updates" that happened after the call
	override def replicate[T : TypeTag, L : TypeTag](path : ActorPath) : Ref[T, L] = {
		val ltt = implicitly[TypeTag[L]]

		if (ltt == typeTag[ConsistencyLevels.Inconsistent]) {
			val remoteMaster = Await.result(actorSystem.actorSelection(path).resolveOne(10 seconds), 12 seconds)
			val localActor =  actorSystem.actorOf(Props(classOf[InconsistentActors.FollowerActor[T]], remoteMaster, typeTag[T]))
			localActor ! Init
			new ObjRef[T, L](localActor)

		} else if (ltt == typeTag[ConsistencyLevels.Weak]) {
			val remoteMaster = Await.result(actorSystem.actorSelection(path).resolveOne(10 seconds), 12 seconds)
			val localActor =  actorSystem.actorOf(Props(classOf[WeakActors.FollowerActor[T]], remoteMaster, typeTag[T]))
			localActor ! Init
			new ObjRef[T, L](localActor)

		} else {
			throw new UnsupportedOperationException("unknown consistency level: " + ltt)
		}


	}

	override def ref[T, L](path : ActorPath) : Ref[T, L] = ???


	private class ObjRef[T, L : TypeTag] (private val objActor : ActorRef) extends Ref[T, L]{

		override def call[R](methodName : String, args : Any*) : R = {
			import akka.pattern.ask

			implicit val timeout : Timeout = Timeout(5 seconds)
			val asked = objActor ? MethodInv(methodName, args)
			val res = Await.result(asked, 5 seconds)
			res.asInstanceOf[R]
		}

		override def getField[R](fieldName : String) : R = {
			import akka.pattern.ask

			implicit val timeout : Timeout = Timeout(5 seconds)
			val asked = objActor ? FieldGet(fieldName)
			val res = Await.result(asked, 5 seconds)
			res.asInstanceOf[R]
		}

		override def setField[R](fieldName : String, value : R) : Unit = {
			objActor ! FieldSet(fieldName, value)
		}

		override def print() : Unit = {
			objActor ! Print
		}
	}
}
