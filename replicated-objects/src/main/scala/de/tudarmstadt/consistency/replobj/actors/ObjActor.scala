package de.tudarmstadt.consistency.replobj.actors

import akka.actor.Actor
import de.tudarmstadt.consistency.replobj.actors.ObjActor.{FieldGet, FieldSet, MethodInv, Print}
import de.tudarmstadt.consistency.replobj.typeToClassTag

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._


/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
abstract class ObjActor[T <: AnyRef](var obj : T, implicit val ttag : TypeTag[T]) extends Actor {

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

	private[actors] trait Message
	private[actors] case class MethodInv(methodName : String, args : Seq[Any]) extends Message
	private[actors] case class FieldGet(fieldName : String) extends Message
	private[actors] case class FieldSet(fieldName : String, newVal : Any) extends Message
	private[actors] case object Init extends Message
	private[actors] case object Replicate extends Message
	private[actors] case object Print extends Message

	private[actors] trait Response
	private[actors] case class Replicated[T](obj : T) extends Response
}
