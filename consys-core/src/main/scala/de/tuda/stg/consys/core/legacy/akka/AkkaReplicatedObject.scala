package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.akka.Requests._
import de.tuda.stg.consys.core.legacy.{ConsistencyLabel, ReflectiveReplicatedObject, Replicated}
import java.lang.reflect.Modifier
import scala.language.postfixOps

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicatedObject[Loc, T] extends ReflectiveReplicatedObject[Loc, T] {

	type ConsistencyLevel = ConsistencyLabel

	protected val replicaSystem : AkkaReplicaSystem {type Addr = Loc}

	override protected def setObject(obj : T) : Unit = {
		super.setObject(obj)
//		replicaSystem.initializeRefFields(obj)
		initializeReplicated()
	}

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
			//Use the top version with unlock (instead of unlockAll) in releaseLock
			//tx.locks.foreach(addr => replicaSystem.releaseLock(addr.asInstanceOf[Addr], tx))
			tx.locks.foreach(addr => replicaSystem.releaseLock(addr.asInstanceOf[Loc], tx))
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

	override def sync() : Unit = {
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
					syncObject(rob.getObject, alreadySynced + rob)

				case ref : AkkaRef[_, _] => //if ref.replicaSystem == replicaSystem =>
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


	/**
	 * Handles a request possibly from another replica system.
	 * This method can be called concurrently.
	 *
	 * @param request The request to be handled
	 *
	 * @return The return value of the request.
	 */
	def handleRequest[R](request : Request[R]) : R = {
		throw new IllegalArgumentException(s"can not handle request $request")
	}



	protected def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
		super.invoke(methodName, args)
	}

	protected def internalGetField[R](tx: Transaction, fldName : String) : R = {
		super.getField(fldName)
	}

	protected def internalSetField(tx: Transaction, fldName : String, newVal : Any) : Unit = {
		super.setField(fldName, newVal)
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
		//throw new UnsupportedOperationException("synchronize not supported on this object")
	}


	protected [akka] def delete() : Unit = { }


	override def toString : String =
		s"AkkaReplicatedObject[$consistencyLevel]($getObject)"


	//Initializes states that implement Replicated
	private def initializeReplicated() : Unit = {
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
}

object AkkaReplicatedObject {
	case object SetFieldAck
	case object SyncAck
}

