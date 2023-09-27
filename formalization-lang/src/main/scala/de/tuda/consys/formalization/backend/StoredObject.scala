package de.tuda.consys.formalization.backend

import de.tuda.consys.formalization.lang.FieldId
import de.tuda.consys.formalization.lang.types.ConsistencyType

class StoredObject(var addr: String,
                   var state: ReplicatedState,
                   var readLevel: ConsistencyType,
                   var timestamps: Map[FieldId, Long]) {
    lazy val newestTimestamp: Long = timestamps.values.max
}
