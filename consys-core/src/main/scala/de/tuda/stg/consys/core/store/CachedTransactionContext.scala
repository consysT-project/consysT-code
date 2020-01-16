package de.tuda.stg.consys.core.store

import scala.collection.mutable
import scala.language.higherKinds
import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CachedTransactionContext extends TransactionContext {

	protected type CachedType[_ <: StoreType#ObjType]

	protected val cache : mutable.Map[StoreType#Addr, CachedType[_]] = mutable.HashMap.empty

	protected def refToCached[T <: StoreType#ObjType : TypeTag](ref : StoreType#RefType[T]) : CachedType[T]

	protected def cachedToRef[T <: StoreType#ObjType : TypeTag](cached : CachedType[T]) : StoreType#RefType[T]

	protected def cacheRef[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, ref : StoreType#RefType[T]) : Unit = {
		cache(addr) = refToCached(ref)
	}


	override def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] = {
		val res = super.replicate[T](addr, obj, level)
		cacheRef(addr, res)
		res
	}

	override def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] = cache.get(addr) match {
		case Some(cachedObject : CachedType[T@unchecked]@unchecked) =>
			cachedToRef[T](cachedObject)
		case None =>
			val res = super.lookup[T](addr, level)
			cacheRef(addr, res)
			res
	}

}
