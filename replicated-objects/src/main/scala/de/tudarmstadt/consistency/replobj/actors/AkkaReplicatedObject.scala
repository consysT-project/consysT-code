package de.tudarmstadt.consistency.replobj.actors

import java.lang.reflect.{Field, Modifier}

import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem._
import de.tudarmstadt.consistency.replobj.actors.Requests._
import de.tudarmstadt.consistency.replobj.{Ref, ReplicatedObject, typeToClassTag}

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


	def setObject(newObj : T) : Unit = {
		state = newObj
		replicaSystem.initializeRefFieldsFor(state)
		ReflectiveAccess.updateObj()
		initialize()
	}

	def getObject : T = state

	/* For overriding only. Do not call this method manually. */
	def initialize() : Unit = { /*do nothing*/	}


	private def transaction[R](f : ContextPath => R) : R = {
		import replicaSystem.GlobalContext

		//Checks whether there is an active transaction
		val isNested = GlobalContext.hasCurrentTransaction
		if (!isNested) GlobalContext.startNewTransaction()

		val path = GlobalContext.getBuilder.nextPath(consistencyLevel)

		GlobalContext.getBuilder.push(consistencyLevel)

		if (!isNested) toplevelTransactionStarted(path)
		else nestedTransactionStarted(path)

		//Execute f
		val result = f(path)

		if (!isNested) toplevelTransactionFinished(path)
		else nestedTransactionFinished(path)

		GlobalContext.getBuilder.pop()

		if (!isNested) GlobalContext.endTransaction()

		result
	}

	protected def toplevelTransactionStarted(ctx : ContextPath) : Unit = { }

	protected def nestedTransactionStarted(ctx : ContextPath) : Unit = { }

	protected def nestedTransactionFinished(ctx : ContextPath) : Unit = { }

	protected def toplevelTransactionFinished(ctx : ContextPath) : Unit = { }


	override final def invoke[R](methodName : String, args : Any*) : R = transaction[R] { path =>
		internalInvoke[R](path, methodName, args)
	}

	override final def getField[R](fieldName : String) : R = transaction[R] { path =>
		internalGetField[R](path, fieldName)
	}

	override final def setField[R](fieldName : String, value : R) : Unit = transaction[Unit] { path =>
		internalSetField(path, fieldName, value)
	}

	override final def sync() : Unit = {

		import replicaSystem.GlobalContext

		GlobalContext.startNewTransaction()
		internalSync()
		GlobalContext.endTransaction()
	}


	override final def syncAll() : Unit = {

		def syncObject(obj : Any, alreadySynced : Set[Any]) : Unit = {
			//TODO:Change contains so that it uses eq?
			if (obj == null || alreadySynced.contains(obj)) {
				return
			}

			obj match {
				case rob : AkkaReplicatedObject[_, _] if rob.replicaSystem == replicaSystem =>
					rob.sync()
					syncObject(rob.state, alreadySynced + rob)

				case ref : RefImpl[_, _] if ref.replicaSystem == replicaSystem =>
					val rob = ref.toReplicatedObject
					syncObject(rob, alreadySynced + ref)

				case _ =>

					val anyClass = obj.getClass
					//If the value is primitive (e.g. int) then stop
					if (anyClass.isPrimitive) {
						return
					}

					//If the value is an array, then initialize ever element of the array.
					if (anyClass.isArray) {
						val anyArray : Array[_] = obj.asInstanceOf[Array[_]]
						val initSet = alreadySynced + obj
						anyArray.foreach(e => syncObject(e, initSet))
					}


					val anyPackage = anyClass.getPackage
					if (anyPackage == null) {
						return
					}

					//If the object should be initialized, then initialize all fields
					anyClass.getDeclaredFields.foreach { field =>
						if ((field.getModifiers & Modifier.STATIC) == 0) { //If field is not static
							//Recursively initialize refs in the fields
							field.setAccessible(true)
							val fieldObj = field.get(obj)
							syncObject(fieldObj, alreadySynced + obj)
						}
					}
			}
		}

		syncObject(this, Set.empty)
	}


	def handleRequest(request : Request) : Any = {
		throw new IllegalArgumentException(s"can not handle request $request")
	}


	def internalInvoke[R](path: ContextPath, methodName: String, args: Seq[Any]) : R = {
		ReflectiveAccess.doInvoke[R](path, methodName, args)
	}

	def internalGetField[R](path : ContextPath, fldName : String) : R = {
		ReflectiveAccess.doGetField(path, fldName)
	}

	def internalSetField(path : ContextPath, fldName : String, newVal : Any) : Unit = {
		ReflectiveAccess.doSetField(path, fldName, newVal)
	}

	final def internalApplyOp[R](op : Operation[R]) : R = op match {
		case GetFieldOp(id, fldName) =>
			internalGetField(id, fldName)

		case SetFieldOp(id, fldName, newVal) =>
			internalSetField(id, fldName, newVal).asInstanceOf[R]

		case InvokeOp(id, mthdName, args) =>
			internalInvoke(id, mthdName, args)
	}


	def internalSync() : Unit = {
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
			val tpe = typeOf[T]
			val mthdTerm = TermName(methodName)

			val methodSymbol = tpe.member(mthdTerm).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)
			val result = methodMirror.apply(args : _*)
			result.asInstanceOf[R]
		}

		def doGetField[R](opid : ContextPath, fieldName : String) : R = ReflectiveAccess.synchronized {
			val tpe = typeOf[T]
			val fldTerm = TermName(fieldName)

			val fieldSymbol = tpe.member(fldTerm).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			val result = fieldMirror.get
			result.asInstanceOf[R]
		}

		def doSetField(opid : ContextPath, fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val fieldSymbol = typeOf[T].member(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			fieldMirror.set(value)
		}
	}






}

object AkkaReplicatedObject {

	case object SetFieldAck
	case object SyncAck
}

