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
	private val opCache : mutable.Map[ContextPath, (Operation[_], Any)] = mutable.HashMap.empty

	protected def clearCache() : Unit = {
		opCache.clear()
	}

	protected def cache[R](op : Operation[R], value : R) : Unit = {
		opCache.put(op.path, (op, value)) match {
			case None => //alles supi!
			case Some(_) => sys.error(s"cannot cache $op. already cached.")
		}
	}

	override def internalInvoke[R](path : ContextPath, methodName : String, args : Seq[Any]) : R =  opCache.get(path) match {
		case None =>
			val res = super.internalInvoke[R](path, methodName, args)
			opCache.put(path, (InvokeOp(path, methodName, args), res))
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == InvokeOp(path, methodName, args))
			cachedResult.asInstanceOf[R]
	}

	override def internalSetField(path : ContextPath, fldName : String, newVal : Any) : Unit = opCache.get(path) match {
		case None =>
			super.internalSetField(path, fldName, newVal)
			opCache.put(path, (SetFieldOp(path, fldName, newVal), ()))


		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == SetFieldOp(path, fldName, newVal))
			println(s"cache hit with $cachedOp")
	}

	override def internalGetField[R](path : ContextPath, fieldName : String) : R =  opCache.get(path) match {
		case None =>
			val res = super.internalGetField[R](path, fieldName)
			opCache.put(path, (GetFieldOp(path, fieldName), res))
			res

		case Some((cachedOp, cachedResult)) =>
			assert(cachedOp == GetFieldOp(path, fieldName))
			println(s"cache hit with $cachedOp: $cachedResult")
			cachedResult.asInstanceOf[R]
	}




}
