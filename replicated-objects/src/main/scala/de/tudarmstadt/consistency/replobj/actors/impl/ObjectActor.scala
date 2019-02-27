package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.impl.ObjectActor._
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, typeToClassTag}

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._


/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
private[actors] trait ObjectActor[T <: AnyRef, L] extends Actor {


	protected var obj : T

	/* dynamic type information */
	protected implicit def objtag : TypeTag[T]
	protected def consistencyTag : TypeTag[L]
	/* predefined for reflection */
	protected implicit lazy val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
	protected lazy val objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)


	def hasConsistency[L0 : TypeTag] : Boolean =
		consistencyTag == typeTag[L0]


	protected def receiveCommand : PartialFunction[Command, Unit] = {
		/* for debugging purposes */
		case Print =>	println("Obj" + this.self + ": " + obj)
	}

	protected def receiveEvent : PartialFunction[Event, Unit] =
		PartialFunction.empty

	override final def receive : Receive = {
		case cmd : Command => receiveCommand(cmd)
		case evt : Event => receiveEvent(evt)
	}


	protected def applyOperation[R](op : Operation[R]) : R = op match {
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


object ObjectActor {

	trait Event

	trait Command
	case class MethodInv(methodName : String, args : Seq[Any]) extends Command
	case class FieldGet(fieldName : String) extends Command
	case class FieldSet(fieldName : String, newVal : Any) extends Command
	case object Print extends Command //Only for debugging


	trait Operation[R]
	case class SetFieldOp(fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[R](mthdName : String, args : Seq[Any]) extends Operation[R]
}
