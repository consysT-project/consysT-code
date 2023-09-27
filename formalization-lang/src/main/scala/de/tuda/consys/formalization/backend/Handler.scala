package de.tuda.consys.formalization.backend

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{Expression, FieldId}
import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType}


class Handler(val txContext: FormalizationTransactionContext, val addr: String, var typ: ClassType)(implicit ct: ClassTable) {
    def invoke(operationLevel: ConsistencyType): Unit = {
        MixedProtocol(txContext.store).invoke(txContext, operationLevel, this)
    }

    def setField(fieldId: FieldId, value: Expression): Unit = {
        MixedProtocol(txContext.store).setField(txContext, this, fieldId, value)
    }

    def getField(fieldId: FieldId): Expression = {
        MixedProtocol(txContext.store).getField(txContext, this, fieldId)
    }
}
