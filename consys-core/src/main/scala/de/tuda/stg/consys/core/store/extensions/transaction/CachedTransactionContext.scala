package de.tuda.stg.consys.core.store.extensions.transaction

import de.tuda.stg.consys.core.store.{Store, TransactionContext}
import java.lang.reflect.Field
import scala.collection.mutable

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CachedTransactionContext[StoreType <: Store] extends TransactionContext[StoreType] {

	protected type CachedType[T <: StoreType#ObjType]

	protected[store] object Cache {
		val buffer : mutable.Map[StoreType#Addr, CacheElement[_ <: StoreType#ObjType]] = mutable.HashMap.empty

		def addEntry[T <: StoreType#ObjType](addr : StoreType#Addr, obj : CachedType[T], changedFields : Iterable[Field] = Iterable.empty) : Unit =
			buffer.put(addr, CacheElement(obj, changedObject = true, changedFields)) match {
				case None =>
				case Some(other) =>
					throw new IllegalStateException(s"object already cached at addr. addr: $addr, obj: $obj, cached: $other")
			}

		def updateEntry[T <: StoreType#ObjType](addr : StoreType#Addr, obj : CachedType[T], changedObject : Boolean, changedFields : Iterable[Field]) : Option[CachedType[T]]  = {
			buffer.get(addr) match {
				case None =>
					buffer.put(addr, CacheElement(obj, changedObject, changedFields)).map(_.data.asInstanceOf[CachedType[T]])
				case Some(prev) =>
					buffer.put(addr, CacheElement(obj, prev.changedObject || changedObject, prev.changedFields ++ changedFields)).map(_.data.asInstanceOf[CachedType[T]])
			}
		}

		/**
		 * Returns an object from the cache. If the object is not present, fetches and writes it to the cache first.
		 */
		def readEntry[T <: StoreType#ObjType](addr : StoreType#Addr, elseFetch : => CachedType[T]) : CachedType[T] =
		  	buffer.getOrElseUpdate(addr, CacheElement[T](elseFetch, changedObject = false, Iterable.empty)).data.asInstanceOf[CachedType[T]]

		/**
		 * Returns an object from the cache if present.
		 */
	  	def readLocalEntry[T <: StoreType#ObjType](addr : StoreType#Addr) : Option[CachedType[T]] =
			buffer.get(addr).map(_.data).asInstanceOf[Option[CachedType[T]]]

		def getChangedFields(addr : StoreType#Addr) : Option[Iterable[Field]] =
			buffer.get(addr).map(_.changedFields)

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
