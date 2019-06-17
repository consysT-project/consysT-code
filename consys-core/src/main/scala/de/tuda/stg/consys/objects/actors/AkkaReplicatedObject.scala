package de.tuda.stg.consys.objects.actors

import java.lang.reflect.{Field, Modifier}

import de.tuda.stg.consys.objects.ReplicatedObject
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem._
import de.tuda.stg.consys.objects.actors.Requests._
import de.tuda.stg.consys.objects.{Ref, ReplicatedObject, typeToClassTag}

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
	}

	protected def getObject : T = state


	private def transaction[R](f : Transaction => R) : R = {
		//Checks whether there is an active transaction
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


	override final def invoke[R](methodName : String, args : Any*) : R = transaction[R] { tx =>
		internalInvoke[R](tx, methodName, args)
	}

	override final def getField[R](fieldName : String) : R = transaction[R] { tx =>
		internalGetField[R](tx, fieldName)
	}

	override final def setField[R](fieldName : String, value : R) : Unit = transaction[Unit] { tx =>
		internalSetField(tx, fieldName, value)
	}

	override final def sync() : Unit = {
		//require(!replicaSystem.hasCurrentTransaction)

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


	def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Any]) : R = {
		ReflectiveAccess.doInvoke[R](methodName, args)
	}

	def internalGetField[R](tx: Transaction, fldName : String) : R = {
		ReflectiveAccess.doGetField(fldName)
	}

	def internalSetField(tx: Transaction, fldName : String, newVal : Any) : Unit = {
		ReflectiveAccess.doSetField(fldName, newVal)
	}

	final def internalApplyOp[R](op : Operation[R]) : R = op match {
		case GetFieldOp(tx, fldName) =>
			internalGetField(tx, fldName)

		case SetFieldOp(tx, fldName, newVal) =>
			internalSetField(tx, fldName, newVal).asInstanceOf[R]

		case InvokeOp(tx, mthdName, args) =>
			internalInvoke(tx, mthdName, args)
	}


	def internalSync() : Unit = {
		throw new UnsupportedOperationException("synchronize not supported on this object")
	}


	override def toString : String =
		s"AkkaReplicatedObject[$consistencyLevel]($state)"


	private final object ReflectiveAccess {

		private implicit val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		//TODO: Define this as field and keep in sync with obj
		private var objMirror : InstanceMirror = _

		private[AkkaReplicatedObject] def updateObj() : Unit = {
			objMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(state)
		}

		def doInvoke[R](methodName : String, args : Seq[Any]) : R = ReflectiveAccess.synchronized {
			val tpe = typeOf[T]
			val mthdTerm = TermName(methodName)

			val methodSymbol = tpe.member(mthdTerm).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)
			val result = methodMirror.apply(args : _*)
			result.asInstanceOf[R]
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

