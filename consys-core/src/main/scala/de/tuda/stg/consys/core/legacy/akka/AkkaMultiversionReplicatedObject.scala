package de.tuda.stg.consys.core.legacy.akka


import de.tuda.stg.consys.core.legacy.akka.Requests.{GetFieldOp, InvokeOp, Operation, SetFieldOp}
import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaMultiversionReplicatedObject[Addr, T] extends AkkaReplicatedObject[Addr, T] {

	//TODO: implement correct garbage collection for multi version cache
	@transient private var _opCache : mutable.Map[Transaction, (Operation[_], Any)] = null
	def opCache : mutable.Map[Transaction, (Operation[_], Any)] = {
		if (_opCache == null) _opCache = mutable.HashMap.empty
		_opCache
	}

	protected def clearCache() : Unit = {
		opCache.clear()
	}

	protected def cache[R](op : Operation[R], value : R) : Unit = {

		if (!requiresCache(op)) {
			return
		}

		opCache.put(op.tx, (op, value)) match {
			case None => //alles supi!
			case Some(_) => replicaSystem.log.warning(s"$op was already cached.")
		}
	}

	protected def requiresCache(op : Operation[_]) : Boolean = true

	override def internalInvoke[R](tx : Transaction, methodName : String, args : Seq[Seq[Any]]) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalInvoke[R](tx, methodName, args)
			cache(InvokeOp(tx, methodName, args), res)
			res

		case Some((cachedOp, cachedResult)) =>
			if (cachedOp != InvokeOp(tx, methodName, args)) {
				//TODO: When does this fail?
//				assert(false, s"expected cached operation to be ${InvokeOp(tx, methodName, args)}, but was $cachedOp")
			}

			cachedResult.asInstanceOf[R]


	}

	override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = opCache.get(tx) match {
		case None =>
			super.internalSetField(tx, fldName, newVal)
			cache(SetFieldOp(tx, fldName, newVal), ())


		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == SetFieldOp(tx, fldName, newVal), s"expected cached operation to be ${SetFieldOp(tx, fldName, newVal)}, but was $cachedOp")
			assert(cachedResult == ())
	}

	override def internalGetField[R](tx : Transaction, fieldName : String) : R =  opCache.get(tx) match {
		case None =>
			val res = super.internalGetField[R](tx, fieldName)
			cache(GetFieldOp(tx, fieldName), res)
			res

		case Some((cachedOp, cachedResult)) =>
			if (cachedOp == GetFieldOp(tx, fieldName)) {
				//TODO: When does this fail?
				//				assert(false, s"expected cached operation to be ${GetFieldOp(tx, fieldName)}, but was $cachedOp")
			}
			cachedResult.asInstanceOf[R]
	}

	override protected def transactionStarted(tx : Transaction) : Unit = {
		super.transactionStarted(tx)
	}

	override protected def transactionFinished(tx : Transaction) : Unit = {
		super.transactionFinished(tx)
	}




}
