package de.tuda.consys.formalization.lang.types

sealed trait ConsistencyType extends TypeLike[ConsistencyType] {
    def <=(t: ConsistencyType): Boolean = ConsistencyTypeLattice(this).hasUpperBound(t)

    def >=(t: ConsistencyType): Boolean = ConsistencyTypeLattice(this).hasLowerBound(t)

    def lub(t: ConsistencyType): ConsistencyType = {
        if (this <= t) t else this // TODO: generalize
    }

    def glb(t: ConsistencyType): ConsistencyType = {
        if (this >= t) t else this // TODO: generalize
    }

    def operationLevel(): OperationLevel
}

case object Local extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case object Strong extends ConsistencyType {
    override def operationLevel(): OperationLevel = StrongOp
}

case object Mixed extends ConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Weak extends ConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Inconsistent extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case object PolyConsistent extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

object ConsistencyTypeLattice {
    private lazy val local: LatticeNode[ConsistencyType] = new LatticeNode(Local, List(strong), List())
    private lazy val strong: LatticeNode[ConsistencyType] = new LatticeNode(Strong, List(mixed), List(local))
    private lazy val mixed: LatticeNode[ConsistencyType] = new LatticeNode(Mixed, List(weak), List(strong))
    private lazy val weak: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(inconsistent), List(mixed))
    private lazy val inconsistent: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(), List(weak))

    def apply(t: ConsistencyType): LatticeNode[ConsistencyType] = t match {
        case Local => local
        case Strong => strong
        case Mixed => mixed
        case Weak => weak
        case Inconsistent => inconsistent
    }
}
