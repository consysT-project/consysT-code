package de.tudarmstadt.consistency.replobj

import akka.actor.{Actor, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.ReplObj._
import de.tudarmstadt.consistency.replobj.classes.A

import scala.concurrent.Await
import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._
import scala.concurrent.duration._



/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
class ReplObj[T : TypeTag](val obj : T)(implicit val actorSystem : ActorSystem) {

	private val actor = actorSystem.actorOf(Props(
		classOf[ObjActor[T]],	obj, typeTag[T]
	))

	/* distribution */
	private val otherReplicas = null


	def call[R](methodName : String, args : Any*) : R = {
		import akka.pattern.ask

		implicit val timeout : Timeout = Timeout(5 seconds)
		val asked = actor ? MethodInv(methodName, args)
		val res = Await.result(asked, 5 seconds)
		res.asInstanceOf[R]
	}

	def field[R](fieldName : String) : FieldOps[R] =
		FieldOps(fieldName)


	case class FieldOps[R] private(fieldName : String) {
		def get : R = {
			import akka.pattern.ask

			implicit val timeout : Timeout = Timeout(5 seconds)
			val asked = actor ? FieldGet(fieldName)
			val res = Await.result(asked, 5 seconds)
			res.asInstanceOf[R]
		}

		def set(value : R) : Unit = {
			actor ! FieldSet(fieldName, value)
		}
	}

	def print() : Unit = {
		actor ! Print
	}



}



object ReplObj {


	class ObjActor[T](val obj : T, implicit val ttag : TypeTag[T]) extends Actor {

		/* predefined for reflection */
		private implicit val ct : ClassTag[T]  = typeToClassTag[T]
		private val objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)

		override def receive : Receive = {
			case MethodInv(mthdName, args) =>
				val res = invoke[Any](mthdName, args : _*)
				sender() ! res
			case FieldGet(fldName) =>
				val res = getField[Any](fldName)
				sender() ! res
			case FieldSet(fldName, value) =>
				setField[Any](fldName, value)


			case Print =>
				/* for debugging purposes */
				println("Obj" + this.self + ": " + obj)
		}

		private def invoke[R](methodName : String, args : Any*) : R = {
			val methodSymbol = typeOf[T].decl(TermName(methodName)).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)

			val result = methodMirror.apply(args : _*)

			result.asInstanceOf[R]
		}

		private def getField[R](fieldName : String) : R = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			val result = fieldMirror.get

			result.asInstanceOf[R]
		}

		private def setField[R](fieldName : String, value : R) : Unit = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			fieldMirror.set(value)
		}
	}



	trait Message
	case class MethodInv(methodName : String, args : Seq[Any]) extends Message
	case class FieldGet(fieldName : String) extends Message
	case class FieldSet(fieldName : String, newVal : Any) extends Message
	case object Print extends Message



	def main(args : Array[String]): Unit = {
		implicit val actorSystem : ActorSystem = ActorSystem("repl")


		val replA : ReplObj[A] = new ReplObj(A())

		replA.call("inc")
		println(replA.call("toString"))
		println(replA.field("f").get)
		replA.field("f").set(10)
		replA.print()


		replA.call("inc")
		replA.print()
	}
}
