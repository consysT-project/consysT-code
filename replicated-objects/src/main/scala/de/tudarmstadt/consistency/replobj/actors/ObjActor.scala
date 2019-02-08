package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, Props}
import de.tudarmstadt.consistency.replobj.actors.ObjActor._
import de.tudarmstadt.consistency.replobj.typeToClassTag

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] class ObjActor[T <: AnyRef](val obj : T, implicit val ttag : TypeTag[T]) extends Actor {

	private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument

//	/* create a new object using reflection */
//	private val obj : T = {
//		val mirror = runtimeMirror(ct.runtimeClass.getClassLoader)
//		val classMirror = mirror.reflectClass(typeOf[T].typeSymbol.asClass)
//		val constructor = classMirror.reflectConstructor(typeOf[T].decl(termNames.CONSTRUCTOR).asMethod)
//
//		constructor.apply(constructorArgs : _*).asInstanceOf[T]
//	}

	/* predefined for reflection */
	private lazy val objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)



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

		/*distributed operations*/
		case Replicate =>
			val replActor = this.context.actorOf(Props(classOf[ObjActor[T]], obj /*TODO: This uses the same object*/, ttag))
			sender() ! obj

		/* for debugging purposes */
		case Print =>
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


object ObjActor {

	private[actors] trait Message
	private[actors] case class MethodInv(methodName : String, args : Seq[Any]) extends Message
	private[actors] case class FieldGet(fieldName : String) extends Message
	private[actors] case class FieldSet(fieldName : String, newVal : Any) extends Message
	private[actors] case object Replicate extends Message
	private[actors] case object Print extends Message
}
