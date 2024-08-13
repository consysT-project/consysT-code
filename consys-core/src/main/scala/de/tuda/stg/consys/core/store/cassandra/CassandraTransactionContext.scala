package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.cql.{BatchStatement, BatchStatementBuilder, BatchType}
import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.cassandra.objects.CassandraObject
import de.tuda.stg.consys.core.store.extensions.coordination.LockingTransactionContext
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect

import java.lang.reflect.Field
import scala.language.implicitConversions
import scala.reflect.ClassTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
abstract class CassandraTransactionContext[StoreType <: CassandraStore](override val store : StoreType) extends TransactionContext[StoreType]
	with CommitableTransactionContext[StoreType]
	with CachedTransactionContext[StoreType, Field]
	with LockingTransactionContext[StoreType] {

	override protected type CachedType[T <: StoreType#ObjType] = CassandraObject[T, _ <: StoreType#Level]

	/** The timestamp of this transaction. It uses the start time of the transaction. */
	//TODO: Is there a better way to generate timestamps for cassandra?
	//TODO: Should we use the commit time instead?
	val startTimestamp : Long = System.currentTimeMillis()

	/** This builder is used for building the commit statement. */
	private var commitStatementBuilder : BatchStatementBuilder = null

	override def replicate[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level, constructorArgs : Any*) : StoreType#RefType[T] = {
		// Creates a new object by calling the matching constructor
		val obj = Reflect.callConstructor[T](implicitly[ClassTag[T]], constructorArgs : _*)

		// Get the matching protocol and execute replicate
		val protocol = level.toProtocol(store)
		val ref = protocol.replicate[T](this, addr, obj)
		ref
	}

	def lookup[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level) : StoreType#RefType[T] = {
		val protocol = level.toProtocol(store)
		val ref = protocol.lookup[T](this, addr)
		ref
	}

	private[store] def getCommitStatementBuilder : BatchStatementBuilder = {
		if (commitStatementBuilder == null)
			throw new IllegalStateException(s"commit statement builder has not been initialized.")
		commitStatementBuilder
	}

	override private[store] def commit() : Unit = {
		/* Compute the timestamp for the batch.
		* 1. Ensure that it is newer than all read timestamps of objects in the buffer.
		* 2. Use the start timestamp of the transaction if it is newer
		*/
		val timestamp = Cache.buffer.valuesIterator.foldLeft(startTimestamp)(
			(timestamp, cassObj) => if (timestamp > cassObj.data.newestTimestamp) timestamp else cassObj.data.newestTimestamp + 1
		)

		// Create a batch statement to batch all the writes
		commitStatementBuilder = BatchStatement.builder(BatchType.LOGGED)
		// Commit every object and gather the writes
		Cache.buffer.valuesIterator.foreach(obj => {
			val protocol = obj.data.consistencyLevel.toProtocol(store)
			protocol.commit(this, obj.data.toRef)
		})

		// Execute the batch statement
		store.cassandra.executeStatement(
			commitStatementBuilder
				.build()
				// Set the timestamp to the creation timestamp of the transactions
				// This avoids "storing" values in weak transactions
				.setQueryTimestamp(timestamp)
		)

		// Reset the batch statement builder
		commitStatementBuilder = null
	}

	override def toString : String = s"CassandraTxContext(${store.id}//$startTimestamp)"

	/** Implicitly resolves handlers in this transaction context. */
	implicit def resolveHandler[T <: CassandraStore#ObjType : ClassTag](ref : CassandraStore#RefType[T]) : CassandraStore#HandlerType[T] =
		ref.resolve(this)
}
