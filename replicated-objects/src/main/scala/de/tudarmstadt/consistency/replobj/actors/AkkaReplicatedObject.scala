package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._
import de.tudarmstadt.consistency.replobj.actors.Context.ContextPath
import de.tudarmstadt.consistency.replobj.actors.Requests._
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
		import replicaSystem.context

		val res = if (context.isEmpty) {
			context.createFresh()

			val request = OpReq(InvokeOp(context.getPath, methodName, args))
			replicaSystem.log(s"invoking method $request in context ${replicaSystem.context.getPath}")

			val tempRes = replicaSystem.request(addr, request)
			context.leave()
			tempRes
		} else {
			context.next()
			context.push()

			val request = OpReq(InvokeOp(context.getPath, methodName, args))
			replicaSystem.log(s"invoking method $request in context ${replicaSystem.context.getPath}")

			val tempRes = replicaSystem.request(addr, request)
			context.pop()
			tempRes
		}

		res.asInstanceOf[R]
	}

	override final def getField[R](fieldName : String) : R = {
		import replicaSystem.context

		val request = if (context.isEmpty) {
			OpReq(GetFieldOp(Context.emptyPath, fieldName))
		} else {
			context.next()
			OpReq(GetFieldOp(context.getNextPath, fieldName))
		}

		replicaSystem.log(s"field get $request in context ${replicaSystem.context.getPath}")

		val res = replicaSystem.request(addr, request)
		res.asInstanceOf[R]
	}

	override final def setField[R](fieldName : String, value : R) : Unit = {
		import replicaSystem.context

		val request = if (context.isEmpty) {
			OpReq(SetFieldOp(Context.emptyPath, fieldName, value))
		} else {
			context.next()
			OpReq(SetFieldOp(context.getNextPath, fieldName, value))
		}

		replicaSystem.log(s"field set $request in context ${replicaSystem.context.getPath}")

		val res = replicaSystem.request(addr, request)
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


		protected final def internalInvoke[R](opid : ContextPath, methodName : String, args : Any*) : R = {
			internalApplyOp(InvokeOp[R](opid, methodName, args))
		}

		protected final def internalGetField[R](opid : ContextPath, fldName : String) : R = {
			internalApplyOp(GetFieldOp[R](opid, fldName))
		}

		protected final def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
			internalApplyOp(SetFieldOp(opid, fldName, newVal))
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
					case GetFieldOp(id, fldName) =>
						val fieldSymbol = typeOf[T].decl(TermName(fldName)).asTerm
						val fieldMirror = objMirror.reflectField(fieldSymbol)
						val result = fieldMirror.get
						result.asInstanceOf[R]

					case SetFieldOp(id, fldName, newVal) =>
						val fieldSymbol = typeOf[T].decl(TermName(fldName)).asTerm
						val fieldMirror = objMirror.reflectField(fieldSymbol)
						fieldMirror.set(newVal).asInstanceOf[R]

					case InvokeOp(id, mthdName, args) =>
						val methodSymbol = typeOf[T].decl(TermName(mthdName)).asMethod
						val methodMirror = objMirror.reflectMethod(methodSymbol)
						val result = methodMirror.apply(args : _*)
						result.asInstanceOf[R]
				}
				result
			}

			@inline def doInvoke[R](opid : ContextPath, methodName : String, args : Any*) : R = {
				applyOp(InvokeOp(opid, methodName, args))
			}

			@inline def doGetField[R](opid : ContextPath, fieldName : String) : R = {
				applyOp(GetFieldOp(opid, fieldName))
			}

			@inline def doSetField(opid : ContextPath, fieldName : String, value : Any) : Unit = {
				applyOp(SetFieldOp(opid, fieldName, value))
			}
		}

	}
}

object AkkaReplicatedObject {



	case object SetFieldAck
	case object SyncAck




}

