package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.Requests.{GetFieldOp, InvokeOp, Operation, SetFieldOp}

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaMultiversionReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T] {

	//TODO: implement correct garbage collection for multi version cache
	private val opCache : mutable.Map[Transaction, (Operation[_], Any)] = mutable.HashMap.empty

	protected def clearCache() : Unit = {
		opCache.clear()
	}

	protected def cache[R](op : Operation[R], value : R) : Unit = {
		opCache.put(op.tx, (op, value)) match {
			case None => //alles supi!
			case Some(_) => sys.error(s"cannot cache $op. already cached.")
		}
	}

	override def internalInvoke[R](tx : Transaction, methodName : String, args : Seq[Any]) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalInvoke[R](tx, methodName, args)
			opCache.put(tx, (InvokeOp(tx, methodName, args), res))
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == InvokeOp(tx, methodName, args))
			cachedResult.asInstanceOf[R]
	}

	override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = opCache.get(tx) match {
		case None =>
			super.internalSetField(tx, fldName, newVal)
			opCache.put(tx, (SetFieldOp(tx, fldName, newVal), ()))


		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == SetFieldOp(tx, fldName, newVal))
	}

	override def internalGetField[R](tx : Transaction, fieldName : String) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalGetField[R](tx, fieldName)
			opCache.put(tx, (GetFieldOp(tx, fieldName), res))
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == GetFieldOp(tx, fieldName))
			cachedResult.asInstanceOf[R]
	}




}
