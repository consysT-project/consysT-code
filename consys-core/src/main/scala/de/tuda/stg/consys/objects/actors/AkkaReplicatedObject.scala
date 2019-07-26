package de.tuda.stg.consys.objects.actors

import java.lang.reflect.{Field, Modifier}

import de.tuda.stg.consys.objects.{Ref, Replicated, ReplicatedObject, typeToClassTag}
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem._
import de.tuda.stg.consys.objects.actors.Requests._
import jdk.internal.dynalink.support.TypeUtilities

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
		replicaSystem.initializeRefFields(state)
		ReflectiveAccess.updateObj()

		intitializeReplicated()
	}

	protected [actors] def getObject : T = state


	private def transaction[R](f : Transaction => R) : R = {
		replicaSystem.newTransaction(consistencyLevel)

		val currentTransaction = replicaSystem.getCurrentTransaction

		transactionStarted(currentTransaction)
		//Execute f
		val result = f(currentTransaction)
		transactionFinished(currentTransaction)

		replicaSystem.commitTransaction()

		result
	}

	protected def transactionStarted(tx : Transaction) : Unit = { }

	protected def transactionFinished(tx : Transaction) : Unit = {
		//Unlock all objects that are locked by this transaction
		if (tx.isToplevel) {
			tx.locks.foreach(addr => replicaSystem.releaseLock(addr.asInstanceOf[Addr], tx))
		}
	}


	override final def invoke[R](methodName : String, args : Seq[Seq[Any]]) : R = transaction[R] { tx =>
		internalInvoke[R](tx, methodName, args)
	}

	override final def getField[R](fieldName : String) : R = transaction[R] { tx =>
		internalGetField[R](tx, fieldName)
	}

	override final def setField[R](fieldName : String, value : R) : Unit = transaction[Unit] { tx =>
		internalSetField(tx, fieldName, value)
	}

	override final def sync() : Unit = {
		require(!replicaSystem.hasCurrentTransaction)

		transaction {
			tx => internalSync()
		}
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

				case ref : AkkaRef[_, _] if ref.replicaSystem == replicaSystem =>
					val rob = ref.deref
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



	protected def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
		ReflectiveAccess.doInvoke[R](methodName, args)
	}

	protected def internalGetField[R](tx: Transaction, fldName : String) : R = {
		ReflectiveAccess.doGetField(fldName)
	}

	protected def internalSetField(tx: Transaction, fldName : String, newVal : Any) : Unit = {
		ReflectiveAccess.doSetField(fldName, newVal)
	}

	protected final def internalApplyOp[R](op : Operation[R]) : R = op match {
		case GetFieldOp(tx, fldName) =>
			internalGetField(tx, fldName)

		case SetFieldOp(tx, fldName, newVal) =>
			internalSetField(tx, fldName, newVal).asInstanceOf[R]

		case InvokeOp(tx, mthdName, args) =>
			internalInvoke(tx, mthdName, args)
	}


	protected def internalSync() : Unit = {
		throw new UnsupportedOperationException("synchronize not supported on this object")
	}


	override def toString : String =
		s"AkkaReplicatedObject[$consistencyLevel]($state)"


	//Initializes states that implement Replicated
	private def intitializeReplicated() : Unit = {

		getObject match {
			case obj : Replicated =>
				//Use reflection to set the field replicaSystem in this class.

				try {
					val field = obj.getClass.getField("replicaSystem")
					field.setAccessible(true)
					field.set(obj, replicaSystem)
				} catch {
					case e : NoSuchFieldException =>
						throw new Exception(s"object of class ${obj.getClass} does not contain field <replicaSystem>. Object:\n$obj", e);
				}
			case _ =>
		}


	}


	private final object ReflectiveAccess {

		private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		//TODO: Define this as field and keep in sync with obj
		private var objMirror : InstanceMirror = _




		private final val rtMirror = runtimeMirror(AkkaReplicatedObject.this.getClass.getClassLoader)

		private[AkkaReplicatedObject] def updateObj() : Unit = {
			objMirror = rtMirror.reflect(state)
		}

		def doInvoke[R](methodName : String, args : Seq[Seq[Any]]) : R = ReflectiveAccess.synchronized {
			val mthdTerm = TermName(methodName)

			val argClasses : Seq[Seq[Class[_]]] = args.map(argList => argList.map(arg => arg.getClass))

			val mbMethodSym : Option[Symbol] = typeOf[T].member(mthdTerm).asTerm.alternatives.find { s =>
				val flattenedParams : Seq[Seq[Class[_]]] =
					s.asMethod.paramLists.map(paramList => paramList.map(param => {
						val classSymbol = param.typeSignature.typeSymbol.asClass
						rtMirror.runtimeClass(classSymbol)
					} ))

				//Check whether parameters can be assigned the given arguments
				flattenedParams.length == argClasses.length && flattenedParams.zip(argClasses).forall(t1 => {
					val (paramList, argList) = t1
					paramList.length == argList.length && paramList.zip(argList).forall(t2 => {
						val (param, arg) = t2

						val result = if (param.isPrimitive) {
							//Treat boxed types correctly: primitive types are converted to boxed types and then checked.
							TypeUtilities.getWrapperType(param).isAssignableFrom(arg)
						} else {
							param.isAssignableFrom(arg)
						}

						result
					})
				})
//				flattenedParams == argClasses
			}

			mbMethodSym match {
				case Some(methodSymbol: MethodSymbol) =>
					val methodMirror = objMirror.reflectMethod(methodSymbol)
					val result = methodMirror.apply(args.flatten : _*)
					result.asInstanceOf[R]
				case _ =>
					throw new NoSuchMethodException(s"method <$methodName> with arguments $args was not found in $objMirror.")
			}
		}

		def doGetField[R](fieldName : String) : R = ReflectiveAccess.synchronized {
			val tpe = typeOf[T]
			val fldTerm = TermName(fieldName)

			val fieldSymbol = tpe.member(fldTerm).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			val result = fieldMirror.get
			result.asInstanceOf[R]
		}

		def doSetField(fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
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

