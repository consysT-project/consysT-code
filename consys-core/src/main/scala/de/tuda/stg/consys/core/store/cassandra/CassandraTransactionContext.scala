package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext, LockingTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect
import scala.language.implicitConversions
import scala.reflect.ClassTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
class CassandraTransactionContext(override val store : CassandraStore) extends TransactionContext[CassandraStore]
	with CommitableTransactionContext[CassandraStore]
	with CachedTransactionContext[CassandraStore]
	with LockingTransactionContext[CassandraStore] {

	override protected type CachedType[T <: CassandraStore#ObjType] = CassandraObject[T, _ <: CassandraStore#Level]

	private[cassandra] val timestamp : Long = System.currentTimeMillis() //TODO: Is there a better way to generate timestamps for cassandra?


	override def replicate[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, level : CassandraStore#Level, constructorArgs : Any*) : CassandraStore#RefType[T] = {
		def callConstructor[T](clazz : ClassTag[T], args : Any*) : T = {
			val constructor = Reflect.findConstructor(clazz.runtimeClass, args : _*)
			constructor.newInstance(args.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[T]
		}

		// Creates a new object by calling the matching constructor
		val obj = callConstructor(implicitly[ClassTag[T]], constructorArgs : _*)

		//
		val protocol = level.toProtocol(store)
		val ref = protocol.replicate[T](this, addr, obj)
		ref

//		store.enref(
//			replicateRaw[T](addr, obj, level)(implicitly[ClassTag[T]]).asInstanceOf[store.RawType[T with store.ObjType]]
//		).asInstanceOf[StoreType#RefType[T]]
	}

	def lookup[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, level : CassandraStore#Level) : CassandraStore#RefType[T] = {
		val protocol = level.toProtocol(store)
		val ref = protocol.lookup[T](this, addr)
		ref

//		store.enref(
//			lookupRaw[T](addr, level)(implicitly[ClassTag[T]]).asInstanceOf[store.RawType[T with store.ObjType]]
//		)(implicitly[ClassTag[T]].asInstanceOf[ClassTag[T with store.ObjType]]).asInstanceOf[StoreType#RefType[T]]
	}

	override private[store] def commit() : Unit = {
		Cache.buffer.valuesIterator.foreach(obj => {
			val protocol = obj.consistencyLevel.toProtocol(store)
			protocol.commit(this, obj.toRef)
		})
		Cache.buffer.valuesIterator.foreach(obj => {
			val protocol = obj.consistencyLevel.toProtocol(store)
			protocol.postCommit(this, obj.toRef)
		})
//		locks.foreach(lock => lock.release())
	}

	override def toString : String = s"CassandraTxContext(${store.id}//$timestamp)"

	/**
	 * Implicitly resolves handlers in this transaction context.
	 */
	implicit def resolveHandler[T <: CassandraStore#ObjType : ClassTag](ref : CassandraStore#RefType[T]) : CassandraStore#HandlerType[T] =
		ref.resolve(this)

}