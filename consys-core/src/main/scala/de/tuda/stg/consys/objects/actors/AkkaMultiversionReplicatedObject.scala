package de.tuda.stg.consys.objects.actors

import de.tuda.stg.consys.objects.actors.Requests.{GetFieldOp, InvokeOp, Operation, SetFieldOp}

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaMultiversionReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T] {

	//TODO: implement correct garbage collection for multi version cache
	protected val opCache : mutable.Map[Transaction, (Operation[_], Any)] = mutable.HashMap.empty

	protected def clearCache() : Unit = {
		opCache.clear()
	}

	protected def cache[R](op : Operation[R], value : R) : Unit = {

		if (!requiresCache(op)) {
			return
		}

		opCache.put(op.tx, (op, value)) match {
			case None => //alles supi!
			case Some(_) => sys.error(s"cannot cache $op. already cached.")
		}
	}

	protected def requiresCache(op : Operation[_]) : Boolean = true

	override def internalInvoke[R](tx : Transaction, methodName : String, args : Seq[Seq[Any]]) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalInvoke[R](tx, methodName, args)
			cache(InvokeOp(tx, methodName, args), res)
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == InvokeOp(tx, methodName, args))
			cachedResult.asInstanceOf[R]
	}

	override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = opCache.get(tx) match {
		case None =>
			super.internalSetField(tx, fldName, newVal)
			cache(SetFieldOp(tx, fldName, newVal), ())


		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == SetFieldOp(tx, fldName, newVal))
			assert(cachedResult == ())
	}

	override def internalGetField[R](tx : Transaction, fieldName : String) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalGetField[R](tx, fieldName)
			cache(GetFieldOp(tx, fieldName), res)
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == GetFieldOp(tx, fieldName))
			cachedResult.asInstanceOf[R]
	}

	override protected def transactionStarted(tx : Transaction) : Unit = {
		super.transactionStarted(tx)
	}

	override protected def transactionFinished(tx : Transaction) : Unit = {
		super.transactionFinished(tx)
	}




}
