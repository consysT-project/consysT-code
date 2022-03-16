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
		val buffer : mutable.Map[StoreType#Addr, CacheElement[_ <: StoreType#ObjType]] = mutable.HashMap.empty

		def writeNewEntry(addr : StoreType#Addr, obj : CachedType[_ <: StoreType#ObjType]) : Unit  = buffer.put(addr, CacheElement(obj, true, Iterable.empty)) match {
			case None =>
			case Some(other) => throw new IllegalStateException(s"object already cached at addr. addr: $addr, obj: $obj, cached: $other")
		}

		def updateEntry[T <: StoreType#ObjType](addr : StoreType#Addr, obj : CachedType[T], changedObject : Boolean, changedFields : Iterable[Field]) : Option[CachedType[T]]  = {
			buffer.get(addr) match {
				case None =>
					buffer.put(addr, CacheElement(obj, changedObject, changedFields)).map(_.data.asInstanceOf[CachedType[T]])
				case Some(prev) =>
					buffer.put(addr, CacheElement(obj, prev.changedObject || changedObject, prev.changedFields ++ changedFields)).map(_.data.asInstanceOf[CachedType[T]])
			}
		}


		def getData[T <: StoreType#ObjType](addr : StoreType#Addr) : Option[CachedType[T]] =
			buffer.get(addr).map(_.data).asInstanceOf[Option[CachedType[T]]]

		def getFields(addr : StoreType#Addr) : Option[Iterable[Field]] =
			buffer.get(addr).map(_.changedFields)

		def getDataAndFields[T <: StoreType#ObjType](addr : StoreType#Addr) : Option[(CachedType[T], Iterable[Field])] =
			buffer.get(addr).map(f => (f.data.asInstanceOf[CachedType[T]], f.changedFields))

		def getOrFetch[T <: StoreType#ObjType](addr : StoreType#Addr,  fetchedObject : => CachedType[T]) : CachedType[T] =
			buffer.getOrElseUpdate(addr, CacheElement[T](fetchedObject, false, Iterable.empty)).data.asInstanceOf[CachedType[T]]

		def setObjectChanged(addr : StoreType#Addr) : Unit = {
			val prev = buffer.getOrElse(addr, throw new IllegalStateException())
			buffer.put(addr, prev.copy(changedObject = true))
		}

		def setFieldsChanged(addr : StoreType#Addr, changedFields : Iterable[Field]) : Unit = {
			val prev = buffer.getOrElse(addr, throw new IllegalStateException())
			buffer.put(addr, prev.copy(changedFields = prev.changedFields ++ changedFields))
		}

		def hasChanges(addr : StoreType#Addr) : Boolean = {
			val prev = buffer.getOrElse(addr, throw new IllegalStateException())
			prev.changedObject || prev.changedFields.nonEmpty
		}

	}

	case class CacheElement[T <: StoreType#ObjType](data : CachedType[T], changedObject : Boolean, changedFields : Iterable[Field])

}

