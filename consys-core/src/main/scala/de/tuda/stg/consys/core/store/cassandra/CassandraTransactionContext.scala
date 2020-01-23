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
	override final type StoreType = CassandraStore
	protected final type CachedType[T <: StoreType#ObjType] = CassandraObject[T]

	val timestamp : Long = System.currentTimeMillis() //TODO: Is there a better way to generate timestamps for cassandra

	override def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] =
		super.replicate(addr, obj, level)

	override def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		super.lookup[T](addr, level)

	override def commit() : Unit = {
		cache.valuesIterator.foreach(obj => obj.writeToStore(store))
		locks.foreach(lock => lock.release())
	}

	override protected def refToCached[T <: StoreType#ObjType : TypeTag](ref : StoreType#RefType[T]) : CachedType[T] =
		ref.resolve(CassandraStores.getCurrentTransaction)

	override protected def cachedToRef[T <: StoreType#ObjType : TypeTag](cached : CachedType[T]) : StoreType#RefType[T] =
		new CassandraHandler[T](cached.addr, cached, cached.consistencyLevel)


	/**
	 * Implicitly resolves handlers in this transaction context.
	 */
	implicit def resolveHandler[T <: StoreType#ObjType : TypeTag](handler : StoreType#RefType[T]) : StoreType#RawType[T] =
		handler.resolve(this)
}