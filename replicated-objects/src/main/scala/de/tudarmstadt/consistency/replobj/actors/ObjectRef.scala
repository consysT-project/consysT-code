package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.Ref
import de.tudarmstadt.consistency.replobj.actors.impl.ObjectActor.{FieldGet, FieldSet, MethodInv, Print}

import scala.concurrent.Await
import scala.reflect.runtime.universe._
import scala.concurrent.duration._
import scala.language.postfixOps

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
@SerialVersionUID(5634024L)
abstract class ObjectRef[T, L : TypeTag](private val objActor : ActorRef) extends Ref[T, L]{

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
