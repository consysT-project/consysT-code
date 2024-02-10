package de.tuda.consys.formalization.backend

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassTable, Expression, FieldId}
import de.tuda.consys.formalization.lang.types.{ConsistencyType, Local, Strong, Weak}

case class MixedProtocol(store: Store)(implicit ct: ClassTable) {
    def replicate(txContext: FormalizationTransactionContext, addr: String, obj: ReplicatedState): Unit  = {
        val fields = obj.fields.keys
        val cassObj = new StoredObject(addr, obj, Local,
            fields.map(f => (f, -1L)).toMap
        )
        txContext.getCache.addEntry(addr, cassObj, fields)
    }

    def invoke(txContext: FormalizationTransactionContext, operationLevel: ConsistencyType, receiver: Handler): Unit = {
        /* Execute a strong method */
        if (operationLevel == Strong || operationLevel == Local) {
            // Lock the object
            txContext.acquireLock(receiver.addr)
            // Lookup the object in the cache
            val addr = receiver.addr

            // Read all fields, since a strong method may access strong and weak fields
            val fields = ClassTable.fields(receiver.typ)
            val cachedObj = txContext.getCache.readEntry(addr, readStrong(addr, fields.keys))

            if (cachedObj.readLevel == Weak) {
                // We have already read all weak fields, so only update strong fields here
                val strongFields = fields.filter(entry => entry._2.typ.l == Strong).keys
                val obj = readStrong(addr, strongFields, Some(cachedObj))
                txContext.getCache.updateEntry(addr, obj, changedObject = false, Iterable.empty)
            }

        } else  {
            // Read all fields, since a weak method may still read strong fields
            val fields = ClassTable.fields(receiver.typ)

            // Lookup the object in the cache
            val addr = receiver.addr
            txContext.getCache.readEntry(addr, readWeak(addr, fields.keys))
        }
    }

    def setField(txContext: FormalizationTransactionContext, receiver: Handler, fieldId: FieldId, value: Expression): Unit = {
        val addr = receiver.addr
        val cachedObject = txContext.getCache.readLocalEntry(addr)
        txContext.getCache.setFieldsChanged(addr, Seq(fieldId))
        cachedObject.get.state.fields += (fieldId -> value)
    }

    def getField(txContext: FormalizationTransactionContext, receiver: Handler, fieldId: FieldId): Expression = {
        val addr = receiver.addr
        val cachedObject = txContext.getCache.readLocalEntry(addr)
        cachedObject.get.state.fields(fieldId)
    }

    def commit(txContext: FormalizationTransactionContext, addr: String): Unit = {
        //TODO: Set consistency level per field
        txContext.getCache.readLocalEntry(addr) zip txContext.getCache.getChangedFields(addr) match {
            case None =>
                throw new IllegalStateException(s"cannot commit $addr. Object not available.")
            case Some((cached: StoredObject, changedFields)) /* if cached.ml == MixedStrong */
                // if any strong field was changed then write batch (all changed fields) with strong consistency
                if cached.readLevel == Strong =>
                val builder = txContext.getCommitStatementBuilder
                store.cassandra.writeFieldEntry(builder, cached.addr, changedFields, cached.state, CassandraLevel.ALL)
            case Some((cached: StoredObject, changedFields)) /* if cached.ml == MixedWeak */ =>
                val builder = txContext.getCommitStatementBuilder
                store.cassandra.writeFieldEntry(builder, cached.addr, changedFields, cached.state, CassandraLevel.ONE)
            case cached =>
                throw new IllegalStateException(s"cannot commit $addr. Object has wrong level, was $cached.")
        }
    }

    private def readStrong(addr: Store#Addr, fields: Iterable[String], cachedObject: Option[StoredObject] = None): StoredObject = {
        val storedObj = store.cassandra.readFieldEntry(addr, fields, CassandraLevel.ALL)
        storedObjToMixedObj(storedObj, Strong, cachedObject)
    }

    private def readWeak(addr: Store#Addr, fields: Iterable[String]): StoredObject = {
        val storedObj = store.cassandra.readFieldEntry(addr, fields, CassandraLevel.ONE)
        storedObjToMixedObj(storedObj, Weak)
    }

    private def storedObjToMixedObj(storedObj: store.cassandra.StoredFieldEntry,
                                    fetchedLevel: ConsistencyType,
                                    cachedObject: Option[StoredObject] = None
                                   ): StoredObject = {
        val instance = cachedObject match {
            case Some(value) => value.state
            case None => new ReplicatedState(Map.empty)
        }

        storedObj.fields.foreach(entry => {
            instance.fields += (entry._1 -> entry._2.asInstanceOf[Expression])
        })

        val cachedTimestamps = cachedObject match {
            case Some(value) => value.timestamps
            case None => Map.empty[FieldId, Long]
        }

        new StoredObject(storedObj.addr, instance, fetchedLevel, cachedTimestamps ++ storedObj.timestamps)
    }
}
