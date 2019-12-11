package de.tuda.stg.consys.experimental.lang.store

import scala.collection.mutable

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CachedTxContext extends TxContext {
	import store._

	protected type CachedType[_ <: ObjType]

	protected val cache : mutable.Map[Addr, CachedType[_]] = mutable.HashMap.empty

	protected def refToCached[T <: ObjType : TypeTag](ref : RefType[T]) : CachedType[T]

	protected def cachedToRef[T <: ObjType : TypeTag](cached : CachedType[T]) : RefType[T]

	override def replicate[T <: ObjType : TypeTag](addr : Addr, obj : T, level : ConsistencyLevel) : RefType[T] = {
		val res = super.replicate(addr, obj, level)
		cache(addr) = refToCached(res)
		res
	}


	override def lookup[T <: ObjType : TypeTag](addr : Addr, level : ConsistencyLevel) : RefType[T] = cache.get(addr) match {
		case Some(cachedObject : CachedType[T@unchecked]@unchecked) =>
			cachedToRef[T](cachedObject)
		case None =>
			val res = super.lookup[T](addr, level)
			cache(addr) = refToCached(res)
			res
	}

}
