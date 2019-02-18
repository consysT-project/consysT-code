package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.Ref
import de.tudarmstadt.consistency.replobj.actors.impl.ObjActor.{FieldGet, FieldSet, MethodInv, Print}

import scala.concurrent.Await
import scala.reflect.runtime.universe._
import scala.concurrent.duration._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
@SerialVersionUID(5634024L)
class ObjRef[T, L : TypeTag] (@transient private val objActor : ActorRef) extends Ref[T, L]{
	//TODO: Is there a way to check whether the actorref references a local actor?
	//Conceptually, ObjRef always has to reference a local actor


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
