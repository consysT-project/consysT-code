package de.tuda.stg.consys.core.store.extensions.transaction

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

	protected type CachedType[T <: StoreType#ObjType]

	protected[store] object Cache {
		val buffer : mutable.Map[StoreType#Addr, CacheElement] = mutable.HashMap.empty

		def put(addr : StoreType#Addr, fields : Iterable[Field] /*  Reflect.getFields(obj.getClass) */, obj : CachedType[_ <: StoreType#ObjType]) : Unit  = buffer.put(addr, CacheElement(obj, fields)) match {
			case None =>
			case Some(other) => throw new IllegalStateException(s"object already cached at addr. addr: $addr, obj: $obj, cached: $other")
		}

		def putForallFields(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Unit =
			put(addr, Reflect.getFields(obj.getClass), obj)

		def putOrOverwrite(addr : StoreType#Addr, fields : Iterable[Field], obj : CachedType[_ <: StoreType#ObjType]) : Option[CachedType[_ <: StoreType#ObjType]]  = {
			buffer.get(addr) match {
				case None =>
					buffer.put(addr, CacheElement(obj, Reflect.getFields(obj.getClass))).map(_.data)
				case Some(prev) =>
					buffer.put(addr, CacheElement(obj, prev.changedFields ++ fields)).map(_.data)

			}
		}


		def getData(addr : StoreType#Addr) : Option[CachedType[_ <: StoreType#ObjType]] =
			buffer.get(addr).map(_.data)

		def getFields(addr : StoreType#Addr) : Option[Iterable[Field]] =
			buffer.get(addr).map(_.changedFields)

		def getDataAndFields(addr : StoreType#Addr) : Option[(CachedType[_ <: StoreType#ObjType], Iterable[Field])] =
			buffer.get(addr).map(f => (f.data, f.changedFields))

		def getOrElseUpdate[T <: StoreType#ObjType](addr : StoreType#Addr, fields : Iterable[Field],  obj : => CachedType[T]) : CachedType[T] =
			buffer.getOrElseUpdate(addr, CacheElement(obj, fields)).asInstanceOf[CachedType[T]]


	}

	case class CacheElement(data : CachedType[_ <: StoreType#ObjType], changedFields : Iterable[Field])

}

