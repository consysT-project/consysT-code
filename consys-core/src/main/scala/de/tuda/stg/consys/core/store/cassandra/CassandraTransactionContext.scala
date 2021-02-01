package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.time.TimestampGenerator
import de.tuda.stg.consys.core.store.{CachedTransactionContext, CommitableTransactionContext, LockingTransactionContext, TransactionContext}

import scala.language.implicitConversions
import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
case class CassandraTransactionContext(store : CassandraStore) extends TransactionContext
	with CassandraTransactionContextBinding
	with CommitableTransactionContext
	with CachedTransactionContext
	with LockingTransactionContext
{
	override type StoreType = CassandraStore
	override protected type CachedType[T <: StoreType#ObjType] = CassandraObject[T]

	private[cassandra] val timestamp : Long = System.currentTimeMillis() //TODO: Is there a better way to generate timestamps for cassandra?

	override private[store] def replicateRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RawType[T] =
		super.replicateRaw[T](addr, obj, level)

	override private[store] def lookupRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RawType[T] =
		super.lookupRaw[T](addr, level)

	//TODO: Can we make this method package private?
	override private[store] def commit() : Unit = {
		cache.valuesIterator.foreach(obj => obj.writeToStore(store))
		locks.foreach(lock => lock.release())
	}

	override protected def rawToCached[T <: StoreType#ObjType : TypeTag](raw : StoreType#RawType[T]) : CachedType[T] = raw

	override protected def cachedToRaw[T <: StoreType#ObjType : TypeTag](cached : CachedType[T]) : StoreType#RawType[T] = cached



	/**
	 * Implicitly resolves handlers in this transaction context.
	 */
	implicit def resolveHandler[T <: StoreType#ObjType : TypeTag](handler : StoreType#RefType[T]) : StoreType#RawType[T] =
		handler.resolve(this)
}