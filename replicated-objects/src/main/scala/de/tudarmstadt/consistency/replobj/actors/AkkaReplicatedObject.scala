package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.{ReplicatedObject, typeToClassTag}

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
abstract class AkkaReplicatedObject[T : TypeTag, L : TypeTag] extends ReplicatedObject[T, L] {

	private[actors] val objActor : ActorRef

	override def invoke[R](methodName : String, args : Any*) : R = {
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



	/*trait for implementing actors of this ref*/
	protected trait ObjectActor extends Actor {

		protected var obj : T

		/* dynamic type information */
//		protected implicit def objtag : TypeTag[T]
		/* predefined for reflection */
		protected implicit lazy val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		protected lazy val objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)


		def hasConsistency[L0 : TypeTag] : Boolean =
			typeTag[L] == typeTag[L0]


		override def receive : Receive = {
			case Print =>	println("Obj" + this.self + ": " + obj)
		}

		protected def applyEvent[R](op : Event[R]) : R = op match {
			case SetFieldOp(fldName, newVal) =>
				setField(fldName, newVal).asInstanceOf[R]
			case InvokeOp(mthdName, args) =>
				invoke[R](mthdName, args)
		}


		protected def invoke[R](methodName : String, args : Any*) : R = {
			val methodSymbol = typeOf[T].decl(TermName(methodName)).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)

			val result = methodMirror.apply(args : _*)

			result.asInstanceOf[R]
		}

		protected def getField[R](fieldName : String) : R = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			val result = fieldMirror.get

			result.asInstanceOf[R]
		}

		protected def setField[R](fieldName : String, value : R) : Unit = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			fieldMirror.set(value)
		}
	}
}


trait Operation
case class MethodInv(methodName : String, args : Seq[Any]) extends Operation
case class FieldGet(fieldName : String) extends Operation
case class FieldSet(fieldName : String, newVal : Any) extends Operation
case object Synchronize extends Operation
case object Print extends Operation //Only for debugging

trait Internal
case class SynchronizeReq(events : Seq[Event[_]]) extends Internal
case class SynchronizeRes(obj : Any) extends Internal




trait Event[R]
case class SetFieldOp(fldName : String, newVal : Any) extends Event[Unit]
case class InvokeOp[R](mthdName : String, args : Seq[Any]) extends Event[R]


