package de.tuda.stg.consys.core.store.extensions.transaction

import de.tuda.stg.consys.core.store.extensions.transaction.CachedTransactionContext.CachedObject
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{Store, TransactionContext}
import java.lang.reflect.Field
import scala.collection.mutable
import scala.language.higherKinds

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CachedTransactionContext[StoreType <: Store] extends TransactionContext[StoreType] {

	type CachedType[T <: StoreType#ObjType] <: CachedObject[StoreType, T]

	protected[store] object Cache {
		val buffer : mutable.Map[StoreType#Addr, CacheElement] = mutable.HashMap.empty

		def put(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Unit  = buffer.put(addr, CacheElement(obj, Reflect.getFields(obj.getClass))) match {
			case None =>
			case Some(other) => throw new IllegalStateException(s"object already cached at addr. addr: $addr, obj: $obj, cached: $other")
		}

		def putOrOverwrite(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Option[CachedType[_ <: StoreType#ObjType]]  = {
			buffer.get(addr) match {
				case None =>
					buffer.put(addr, CacheElement(obj, Reflect.getFields(obj.getClass))).map(_.data)
				case Some(prev) =>

			}
		}


		def get(addr : StoreType#Addr) : Option[CachedType[_ <: StoreType#ObjType]] =
			buffer.get(addr)

		def getOrElseUpdate[T <: StoreType#ObjType](addr : StoreType#Addr,  obj : => CachedType[T]) : CachedType[T] =
			buffer.getOrElseUpdate(addr, obj).asInstanceOf[CachedType[T]]

		private def objectToMap()

	}

	private case class CacheElement(data : CachedType[_ <: StoreType#ObjType], changedFields : Iterable[Field])

}

object CachedTransactionContext {
	trait CachedObject[StoreType <: Store, T <: StoreType#ObjType] {
		def state : T
	}
}
