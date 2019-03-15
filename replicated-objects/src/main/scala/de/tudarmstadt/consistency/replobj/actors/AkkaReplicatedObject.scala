package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
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
trait AkkaReplicatedObject[Addr, T <: AnyRef] extends ReplicatedObject[T] {

	protected val replicaSystem : AkkaReplicaSystem[Addr]

	protected implicit def ttt : TypeTag[T]

	val addr : Addr

	private var state : T = _


	protected def setObject(newObj : T) : Unit = {
		state = newObj
		replicaSystem.initializeRefFieldsFor(state)
		ReflectiveAccess.updateObj()
		initialize()
	}

	protected def getObject : T = state

	/* For overriding only. Do not call this method manually. */
	protected def initialize() : Unit = { /*do nothing*/	}



	override final def invoke[R](methodName : String, args : Any*) : R = {
		import replicaSystem.GlobalContext

		val needNewTx = !GlobalContext.hasBuilder

		if (needNewTx) GlobalContext.startNewTransaction()


		val path = GlobalContext.getBuilder.nextPath(consistencyLevel)
		replicaSystem.log(s"invoking method $addr.$methodName(${args.mkString(", ")}) in context $path")

		GlobalContext.getBuilder.push(consistencyLevel)
		val res : R = internalInvoke[R](path, methodName, args)
		GlobalContext.getBuilder.pop()

		if (needNewTx) GlobalContext.endTransaction()
		res.asInstanceOf[R]
	}


	override final def getField[R](fieldName : String) : R = {
		import replicaSystem.GlobalContext

		val needNewTx = !GlobalContext.hasBuilder

		if (needNewTx) GlobalContext.startNewTransaction()

		val path = GlobalContext.getBuilder.nextPath(consistencyLevel)
		replicaSystem.log(s"getting field $addr.$fieldName in context $path")

		val res = internalGetField[R](path, fieldName)

		if (needNewTx)GlobalContext.endTransaction()

		res.asInstanceOf[R]
	}

	override final def setField[R](fieldName : String, value : R) : Unit = {
		import replicaSystem.GlobalContext

		val needNewTx = !GlobalContext.hasBuilder

		if (needNewTx) GlobalContext.startNewTransaction()


		val path = GlobalContext.getBuilder.nextPath(consistencyLevel)
		replicaSystem.log(s"setting field $addr.$fieldName = $value in context $path")

		internalSetField(path, fieldName, value)

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
		ReflectiveAccess.doInvoke[R](path, methodName, args)
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






}

object AkkaReplicatedObject {

	case object SetFieldAck
	case object SyncAck
}

