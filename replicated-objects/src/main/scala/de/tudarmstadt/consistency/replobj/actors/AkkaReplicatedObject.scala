package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._
import de.tudarmstadt.consistency.replobj.{ReplicatedObject, typeToClassTag}

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe
import scala.reflect.runtime.universe._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
abstract class AkkaReplicatedObject[T <: AnyRef : TypeTag, L : TypeTag] extends ReplicatedObject[T, L] {

	private[actors] val objActor : ActorRef

	protected val replicaSystem : AkkaReplicaSystem[_]

	override def invoke[R](methodName : String, args : Any*) : R = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(60 seconds)
		val asked = objActor ? MethodInv(methodName, args)
		val res = Await.result(asked, 60 seconds)
		res.asInstanceOf[R]
	}

	override def getField[R](fieldName : String) : R = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(10 seconds)
		val asked = objActor ? FieldGet(fieldName)
		val res = Await.result(asked, 10 seconds)
		res.asInstanceOf[R]
	}

	override def setField[R](fieldName : String, value : R) : Unit = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(10 seconds)
		val asked = objActor ? FieldSet(fieldName, value)
		Await.ready(asked, 10 seconds)
	}

	override def print() : Unit = {
		objActor ! Print
	}

	override def getConsistencyLevel : TypeTag[L] =
		implicitly[TypeTag[L]]



	/*trait for implementing actors of this ref*/
	protected trait ObjectActor extends Actor {

		protected var obj : T

		/* dynamic type information */
//		protected implicit def objtag : TypeTag[T]
		/* predefined for reflection */
		protected implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		protected var objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)


		protected def setObject(newObj : T) : Unit = {
			replicaSystem.initializeRefFields(newObj)
			obj = newObj
			objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)
		}

		def hasConsistency[L0 : TypeTag] : Boolean =
			typeTag[L] == typeTag[L0]


		override def receive : Receive = {
			case Print =>	println("Obj" + this.self + ": " + obj)
		}

		protected def applyEvent[R](op : Event[R]) : R = {

			val result : R = op match {
				case GetFieldOp(fldName) =>
					val fieldSymbol = typeOf[T].decl(TermName(fldName)).asTerm
					val fieldMirror = objMirror.reflectField(fieldSymbol)
					val result = fieldMirror.get
					result.asInstanceOf[R]

				case SetFieldOp(fldName, newVal) =>
					val fieldSymbol = typeOf[T].decl(TermName(fldName)).asTerm
					val fieldMirror = objMirror.reflectField(fieldSymbol)
					fieldMirror.set(newVal).asInstanceOf[R]

				case InvokeOp(mthdName, args) =>
					val methodSymbol = typeOf[T].decl(TermName(mthdName)).asMethod
					val methodMirror = objMirror.reflectMethod(methodSymbol)
					val result = methodMirror.apply(args : _*)
					result.asInstanceOf[R]
			}


			result
		}


		protected def invoke[R](methodName : String, args : Any*) : R = {
			applyEvent(InvokeOp(methodName, args))
		}

		protected def getField[R](fieldName : String) : R = {
			applyEvent(GetFieldOp(fieldName))
		}

		protected def setField[R](fieldName : String, value : R) : Unit = {
			applyEvent(SetFieldOp(fieldName, value))
		}
	}
}

object AkkaReplicatedObject {

	sealed trait Operation
	case class MethodInv(methodName : String, args : Seq[Any]) extends Operation
	case class FieldGet(fieldName : String) extends Operation
	case class FieldSet(fieldName : String, newVal : Any) extends Operation
	case object Synchronize extends Operation
	case object Print extends Operation //Only for debugging

	case object SetAck


	sealed trait Event[R]
	case class GetFieldOp[R](fldName : String) extends Event[R]
	case class SetFieldOp(fldName : String, newVal : Any) extends Event[Unit]
	case class InvokeOp[R](mthdName : String, args : Seq[Any]) extends Event[R]


}

