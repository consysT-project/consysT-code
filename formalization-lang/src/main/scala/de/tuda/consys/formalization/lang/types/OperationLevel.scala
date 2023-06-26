package de.tuda.consys.formalization.lang.types

sealed trait OperationLevel {
    def consistencyType(): ConsistencyType
}

case object StrongOp extends OperationLevel {
    override def consistencyType(): ConsistencyType = Strong
}

case object WeakOp extends OperationLevel {
    override def consistencyType(): ConsistencyType = Weak
}
