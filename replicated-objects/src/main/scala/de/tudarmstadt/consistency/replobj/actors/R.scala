package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.ObjActor._
import de.tudarmstadt.consistency.replobj.classes.{A, B}
import de.tudarmstadt.consistency.replobj.typeToClassTag

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._



/**
	* Wraps ActorRefs to ObjActors. There is no functionality other than
	* providing a nice syntax to use ObjActors.
	*
	* @author Mirko Köhler
	*/
class R[T : TypeTag] private(
		private val objActor : ActorRef
	) {


	def call[R](methodName : String, args : Any*) : R = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(5 seconds)
		val asked = objActor ? MethodInv(methodName, args)
		val res = Await.result(asked, 5 seconds)
		res.asInstanceOf[R]
	}

	def fieldGet[R](fieldName : String) : R = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(5 seconds)
		val asked = objActor ? FieldGet(fieldName)
		val res = Await.result(asked, 5 seconds)
		res.asInstanceOf[R]
	}

	def fieldSet[R](fieldName : String, value : R) : Unit = {
		objActor ! FieldSet(fieldName, value)
	}

	def replicate() : T = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(5 seconds)
		val asked = objActor ? Replicate
		val res = Await.result(asked, 5 seconds)


//		new R(res.asInstanceOf[ActorRef])
		res.asInstanceOf[T]
	}

	def print() : Unit = {
		objActor ! Print
	}

	/* syntactic sugar*/
	def apply[R](fieldName : String) : R =
		fieldGet(fieldName)

	def update[R](fieldName : String, value : R) : Unit =
		fieldSet(fieldName, value)

	def <=[R](methodName : String, args : Any*) : R =
		call[R](methodName, args : _*)

	def ! : T = replicate()


}

object R {

	def create[T : TypeTag](obj : T)(implicit actorSystem : ActorSystem) : R[T] = {
		val actorRef = actorSystem.actorOf(Props(classOf[ObjActor[T]],	obj, typeTag[T]))
		new R(actorRef)
	}

}


