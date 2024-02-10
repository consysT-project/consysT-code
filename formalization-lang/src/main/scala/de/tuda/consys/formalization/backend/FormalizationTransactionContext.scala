package de.tuda.consys.formalization.backend

import com.datastax.oss.driver.api.core.cql.{BatchStatement, BatchStatementBuilder, BatchType}
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.types.ClassType
import de.tuda.consys.formalization.lang.{Expression, FieldId}
import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.extensions.coordination.ZookeeperLockingTransactionContext
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}

import scala.reflect.ClassTag

class FormalizationTransactionContext(override val store: Store)(implicit ct: ClassTable) extends TransactionContext[Store]
    with CommitableTransactionContext[Store]
    with CachedTransactionContext[Store, FieldId]
    with ZookeeperLockingTransactionContext[Store] {

    def getCache: Cache.type = Cache

    override protected type CachedType[T <: Store#ObjType] = StoredObject

    val startTimestamp: Long = System.currentTimeMillis()

    /** This builder is used for building the commit statement. */
    private var commitStatementBuilder: BatchStatementBuilder = null

    def replicateNew(addr: Store#Addr, typ: ClassType, constructorArgs: Map[FieldId, Expression]): Handler = {
        val obj = new ReplicatedState(constructorArgs)
        MixedProtocol(store).replicate(this, addr, obj)
        new Handler(this, addr, typ)
    }

    def getCommitStatementBuilder: BatchStatementBuilder = {
        if (commitStatementBuilder == null)
            throw new IllegalStateException(s"commit statement builder has not been initialized.")
        commitStatementBuilder
    }

    override def commit(): Unit = {
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
            MixedProtocol(store).commit(this, obj.data.addr)
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

    def resolveHandler(addr: String, typ: ClassType): Handler = new Handler(this, addr, typ)

    override def replicate[T <: Store#ObjType : ClassTag](addr: FieldId, level: Store#Level, constructorArgs: Any*): Store#RefType[T] = ???

    override def lookup[T <: Store#ObjType : ClassTag](addr: FieldId, level: Store#Level): Store#RefType[T] = ???
}
