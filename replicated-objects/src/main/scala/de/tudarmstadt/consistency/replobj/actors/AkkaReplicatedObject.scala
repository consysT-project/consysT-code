package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{Actor, ActorRef}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject._
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

	protected val replicaSystem : AkkaReplicaSystem[Addr]

	protected implicit def ttt : TypeTag[T]
	protected implicit def ltt : TypeTag[L]


	val addr : Addr

	private var state : T = _


	protected def setObject(newObj : T) : Unit = {
		state = newObj
		initializeRefFields()
		ReflectiveAccess.updateObj()
		initialize()
	}

	protected def getObject : T = state

	/* For overriding only. Do not call this method manually. */
	protected def initialize() : Unit = { /*do nothing*/	}



	override def getConsistencyLevel : TypeTag[L] = ltt




	override final def invoke[R](methodName : String, args : Any*) : R = {
		import replicaSystem.GlobalContext

		val needNewTx = GlobalContext.isEmpty

		if (needNewTx) GlobalContext.startNewTransaction()


		val path = GlobalContext.getCurrentPath
		replicaSystem.log(s"invoking method $addr.$methodName(${args.mkString(", ")}) in context $path")

		val res : R = internalInvoke[R](path, methodName, args)

		GlobalContext.set(_.next())

		if (needNewTx) GlobalContext.endTransaction()
		res.asInstanceOf[R]
	}


	override final def getField[R](fieldName : String) : R = {
		import replicaSystem.GlobalContext

		val needNewTx = GlobalContext.isEmpty

		if (needNewTx) GlobalContext.startNewTransaction()


		val path = GlobalContext.getCurrentPath
		replicaSystem.log(s"getting field $addr.$fieldName in context $path")

		val res = internalGetField[R](path, fieldName)

		GlobalContext.set(_.next())
		if (needNewTx)GlobalContext.endTransaction()

		res.asInstanceOf[R]
	}

	override final def setField[R](fieldName : String, value : R) : Unit = {
		import replicaSystem.GlobalContext

		val needNewTx = GlobalContext.isEmpty

		if (needNewTx) GlobalContext.startNewTransaction()


		val path = GlobalContext.getCurrentPath
		replicaSystem.log(s"setting field $addr.$fieldName = $value in context $path")

		internalSetField(path, fieldName, value)

		GlobalContext.set(_.next())
		if (needNewTx) GlobalContext.endTransaction()

	}

	override final def sync() : Unit = {

		import replicaSystem.GlobalContext

		GlobalContext.startNewTransaction()
		internalSync()
		GlobalContext.endTransaction()
	}


	def handleRequest(request : Request) : Any = {
		throw new IllegalArgumentException(s"can not handle request $request")
	}


	protected def internalInvoke[R](path: ContextPath, methodName: String, args: Seq[Any]) : R = {
		import replicaSystem.GlobalContext

		GlobalContext.set(_.push())
		val res = ReflectiveAccess.doInvoke[R](path, methodName, args)
		GlobalContext.set(_.pop())

		res
	}

	protected def internalGetField[R](path : ContextPath, fldName : String) : R = {
		ReflectiveAccess.doGetField(path, fldName)
	}

	protected def internalSetField(path : ContextPath, fldName : String, newVal : Any) : Unit = {
		ReflectiveAccess.doSetField(path, fldName, newVal)
	}

	protected final def internalApplyOp[R](op : Operation[R]) : R = op match {
		case GetFieldOp(id, fldName) =>
			internalGetField(id, fldName)

		case SetFieldOp(id, fldName, newVal) =>
			internalSetField(id, fldName, newVal).asInstanceOf[R]

		case InvokeOp(id, mthdName, args) =>
			internalInvoke(id, mthdName, args)
	}


	protected def internalSync() : Unit = {
		throw new UnsupportedOperationException("synchronize not supported on this object")
	}





	private final object ReflectiveAccess {

		private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		//TODO: Define this as field and keep in sync with obj
		private var objMirror : InstanceMirror = _

		private[AkkaReplicatedObject] def updateObj() : Unit = {
			objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(state)
		}

		def doInvoke[R](opid : ContextPath, methodName : String, args : Seq[Any]) : R = ReflectiveAccess.synchronized {
			val methodSymbol = typeOf[T].decl(TermName(methodName)).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)
			val result = methodMirror.apply(args : _*)
			result.asInstanceOf[R]
		}

		def doGetField[R](opid : ContextPath, fieldName : String) : R = ReflectiveAccess.synchronized {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			val result = fieldMirror.get
			result.asInstanceOf[R]
		}

		def doSetField(opid : ContextPath, fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			fieldMirror.set(value)
		}
	}





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

		initializeObject(state)
	}
}

object AkkaReplicatedObject {

	case object SetFieldAck
	case object SyncAck
}

