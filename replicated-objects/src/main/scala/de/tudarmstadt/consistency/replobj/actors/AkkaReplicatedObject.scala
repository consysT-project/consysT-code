package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
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


	override final def invoke[R](methodName : String, args : Any*) : R = {
		val res = replicaSystem.request(addr, InvokeReq(methodName, args))
		res.asInstanceOf[R]
	}

	override final def getField[R](fieldName : String) : R = {
		val res = replicaSystem.request(addr, GetFieldReq(fieldName))
		res.asInstanceOf[R]
	}

	override final def setField[R](fieldName : String, value : R) : Unit = {
		val res = replicaSystem.request(addr, SetFieldReq(fieldName, value))
		assert(res == SetFieldAck)
	}

	override final def sync() : Unit = {
		val res = replicaSystem.request(addr, SyncReq)
		assert(res == SyncAck)
	}

	override def getConsistencyLevel : TypeTag[L] = ltt




	/*trait for implementing actors of this ref*/
	protected trait ObjectActor extends Actor {

		private var obj : T = null.asInstanceOf[T]


		protected def setObject(newObj : T) : Unit = {
			obj = newObj
			initializeRefFields()
			ReflectiveAccess.updateObj()
			initialize()
		}

		protected def getObject : T =
			obj

		/* For overriding only. Do not call this method manually. */
		protected def initialize() : Unit = { /*do nothing*/	}


		private def initializeRefFields() : Unit = {

			def initializeObject(any : AnyRef) : Unit = {
				require(any != null, "cannot initialize null object")

				any.getClass.getDeclaredFields.foreach { field =>

					val fieldType = field.getType

					//Field is a ref => initialize the replica system
					if (fieldType.isAssignableFrom(classOf[RefImpl[_,_,_]])) {
						field.setAccessible(true)
						field.get(any) match {
							case null =>
							case refImpl : RefImpl[Addr, _, _] =>
								refImpl.replicaSystem = replicaSystem
							case x =>
								sys.error(s"cannot initialize unknown implementation of Ref: $x")
						}
					}
					//Field is an object => recursively initialize refs in that object
					//TODO: Exclude java/scala library classes?
					else if (!fieldType.isPrimitive && !fieldType.isArray && !fieldType.isSynthetic) {
						field.setAccessible(true)
						field.get(any) match {
							case null =>
							case someObj =>
								initializeObject(someObj)
						}
					}
				}
			}

			initializeObject(obj)


		}


		protected final def internalInvoke[R](methodName : String, args : Any*) : R = {
			internalApplyOp(InvokeOp[R](methodName, args))
		}

		protected final def internalGetField[R](fldName : String) : R = {
			internalApplyOp(GetFieldOp[R](fldName))
		}

		protected final def internalSetField(fldName : String, newVal : Any) : Unit = {
			internalApplyOp(SetFieldOp(fldName, newVal))
		}

		protected def internalApplyOp[R](op : Operation[R]) : R = {
			ReflectiveAccess.applyOp(op)
		}


		private final object ReflectiveAccess {

			private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
			//TODO: Define this as field and keep in sync with obj
			private var objMirror : InstanceMirror = null

			private[ObjectActor] def updateObj() : Unit = {
				objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)
			}

			def applyOp[R](op : Operation[R]) : R = ObjectActor.this.synchronized {
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

			@inline def doSetField(fieldName : String, value : Any) : Unit = {
				applyOp(SetFieldOp(fieldName, value))
			}
		}

	}
}

object AkkaReplicatedObject {



	case object SetFieldAck
	case object SyncAck

	sealed trait Operation[+R]
	case class GetFieldOp[+R](fldName : String) extends Operation[R]
	case class SetFieldOp(fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](mthdName : String, args : Seq[Any]) extends Operation[R]


}

