package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem.{RefImpl, Request, ReturnRequest}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._
import de.tudarmstadt.consistency.replobj.{ReplicatedObject, typeToClassTag}

import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicatedObject[Addr, T <: AnyRef, L] extends ReplicatedObject[T, L] {

	val addr : Addr

	private[actors] val objActor : ActorRef
	protected val replicaSystem : AkkaReplicaSystem[Addr]

	protected implicit def ttt : TypeTag[T]
	protected implicit def ltt : TypeTag[L]


	//TODO: Sending requests may lead to deadlocks, just call the methods instead
	override def invoke[R](methodName : String, args : Any*) : R = {
		val res = replicaSystem.request(addr, InvokeReq(methodName, args))
		res.asInstanceOf[R]
	}

	override def getField[R](fieldName : String) : R = {
		val res = replicaSystem.request(addr, GetFieldReq(fieldName))
		res.asInstanceOf[R]
	}

	override def setField[R](fieldName : String, value : R) : Unit = {
		val res = replicaSystem.request(addr, SetFieldReq(fieldName, value))
		res.asInstanceOf[Unit]
	}

	override def sync() : Unit = {
		val res = replicaSystem.request(addr, SyncReq)
		res.asInstanceOf[Unit]
	}

	override def getConsistencyLevel : TypeTag[L] = ltt



	/*trait for implementing actors of this ref*/
	protected trait ObjectActor extends Actor {

		private var obj : T = null.asInstanceOf[T]


		protected def setObject(newObj : T) : Unit = {
			obj = newObj
			initializeRefFields()
			ReflectiveAccess.updateObj()
		}

		protected def getObject : T =
			obj


		private def initializeRefFields() : Unit = {
			obj.getClass.getDeclaredFields.foreach { field =>
				if (field.getType.isAssignableFrom(classOf[RefImpl[_,_,_]])) {
					field.setAccessible(true)
					field.get(obj) match {
						case refImpl : RefImpl[Addr, _, _] =>
							refImpl.replicaSystem = replicaSystem
						case _ =>
					}
				}
				//TODO: Check recursively for ref fields. Care for cycles (fields of type of the class the declares it)
			}
		}

		protected final object ReflectiveAccess {

			private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
			//TODO: Define this as field and keep in sync with obj
			private var objMirror : InstanceMirror = null

			private[ObjectActor] def updateObj() : Unit = {
				objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)
			}

			def applyOp[R](op : Operation[R]) : R = synchronized {
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

			@inline def doInvoke[R](methodName : String, args : Any*) : R = {
				applyOp(InvokeOp(methodName, args))
			}

			@inline def doGetField[R](fieldName : String) : R = {
				applyOp(GetFieldOp(fieldName))
			}

			@inline def doSetField[R](fieldName : String, value : R) : Unit = {
				applyOp(SetFieldOp(fieldName, value))
			}
		}

	}
}

object AkkaReplicatedObject {

	sealed trait ObjectReq extends Request
	case class InvokeReq(methodName : String, args : Seq[Any]) extends ObjectReq with ReturnRequest
	case class GetFieldReq(fieldName : String) extends ObjectReq with ReturnRequest
	case class SetFieldReq(fieldName : String, newVal : Any) extends ObjectReq with ReturnRequest
	case object SyncReq extends ObjectReq with ReturnRequest

	sealed trait Operation[+R]
	case class GetFieldOp[+R](fldName : String) extends Operation[R]
	case class SetFieldOp(fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](mthdName : String, args : Seq[Any]) extends Operation[R]


}

