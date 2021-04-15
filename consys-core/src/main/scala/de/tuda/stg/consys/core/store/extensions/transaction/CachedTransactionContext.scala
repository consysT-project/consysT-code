package de.tuda.stg.consys.core.store.extensions.transaction

import de.tuda.stg.consys.core.store.{Store, TransactionContext}
import scala.collection.mutable
import scala.language.higherKinds

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CachedTransactionContext[StoreType <: Store] extends TransactionContext[StoreType] {

	protected type CachedType[_ <: StoreType#ObjType]

	protected[store] object Cache {
		val buffer : mutable.Map[StoreType#Addr, CachedType[_ <: StoreType#ObjType]] = mutable.HashMap.empty

		def put(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Unit  = buffer.put(addr, obj) match {
			case None =>
			case Some(other) => throw new IllegalStateException(s"object already cached at addr. addr: $addr, obj: $obj, cached: $other")
		}

		def putOrOverwrite(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Option[CachedType[_ <: StoreType#ObjType]]  =
			buffer.put(addr, obj)

		def get(addr : StoreType#Addr) : Option[CachedType[_ <: StoreType#ObjType]] =
			buffer.get(addr)

		def getOrElseUpdate[T <: StoreType#ObjType](addr : StoreType#Addr,  obj : => CachedType[T]) : CachedType[T] =
			buffer.getOrElseUpdate(addr, obj).asInstanceOf[CachedType[T]]
	}


}
