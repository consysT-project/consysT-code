package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorPath, ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.DistributedStore
import de.tudarmstadt.consistency.replobj.actors.impl.ObjActor.{FieldGet, FieldSet, MethodInv, Print}

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait ActorStore extends DistributedStore[String, ActorPath] {

	implicit val actorSystem : ActorSystem


	override def distribute[T : TypeTag, L : TypeTag](addr : String, value : T) : Ref[T, L] =
		throw new UnsupportedOperationException("unknown consistency level: " + implicitly[TypeTag[L]])


		//TODO: replicate can return even though the state replication has not finished yet. Thus it can include "future updates" that happened after the call
	override def replicate[T : TypeTag, L : TypeTag](path : ActorPath) : Ref[T, L] =
		throw new UnsupportedOperationException("unknown consistency level: " + implicitly[TypeTag[L]])


	protected def getMaster(path : ActorPath) : ActorRef = {
		Await.result(actorSystem.actorSelection(path).resolveOne(10 seconds), 12 seconds)
	}


	protected class ObjRef[T, L : TypeTag] (private val objActor : ActorRef) extends Ref[T, L]{

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
