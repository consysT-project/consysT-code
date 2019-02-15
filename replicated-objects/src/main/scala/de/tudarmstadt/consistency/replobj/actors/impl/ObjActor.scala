package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.impl.ObjActor.{FieldGet, FieldSet, MethodInv, Print}
import de.tudarmstadt.consistency.replobj.typeToClassTag

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._


/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] trait ObjActor[T <: AnyRef, L] extends Actor {

	protected var obj : T
	protected implicit def objtag : TypeTag[T]
	protected def consistencyTag : TypeTag[L]

	/* predefined for reflection */
	protected implicit lazy val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
	protected lazy val objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)


	override def receive : Receive = {
		/*object operations*/
		case MethodInv(mthdName, args) =>
			val res = invoke[Any](mthdName, args : _*)
			sender() ! res
		case FieldGet(fldName) =>
			val res = getField[Any](fldName)
			sender() ! res
		case FieldSet(fldName, value) =>
			setField[Any](fldName, value)

		/* for debugging purposes */
		case Print =>
			println("Obj" + this.self + ": " + obj)
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


object ObjActor {

	trait Message

	sealed trait ObjectMessage extends Message
	case class MethodInv(methodName : String, args : Seq[Any]) extends ObjectMessage
	case class FieldGet(fieldName : String) extends ObjectMessage
	case class FieldSet(fieldName : String, newVal : Any) extends ObjectMessage

	sealed trait DebugMessage extends Message
	case object Print extends DebugMessage
}
