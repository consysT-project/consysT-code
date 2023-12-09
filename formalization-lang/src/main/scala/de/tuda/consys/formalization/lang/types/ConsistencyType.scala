package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ConsistencyVarEnv, ConsistencyVarId, TypeVarEnv, TypeVarMutabilityEnv}

sealed trait ConsistencyType extends TypeLike[ConsistencyType] {
    def operationLevel(): OperationLevel

    def <=(t: ConsistencyType)(implicit classTable: ClassTable,
                               typeVarEnv: TypeVarEnv,
                               typeVarMutabilityEnv: TypeVarMutabilityEnv,
                               consistencyVarEnv: ConsistencyVarEnv): Boolean =
        Subtyping.subtype(this, t)

    def >=(t: ConsistencyType)(implicit classTable: ClassTable,
                               typeVarEnv: TypeVarEnv,
                               typeVarMutabilityEnv: TypeVarMutabilityEnv,
                               consistencyVarEnv: ConsistencyVarEnv): Boolean =
        Subtyping.subtype(t, this)
}

sealed trait ConcreteConsistencyType extends ConsistencyType

case object Local extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = StrongOp
}

case object Strong extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = StrongOp
}

case object Weak extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Inconsistent extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case class ConsistencyVar(name: ConsistencyVarId) extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???

    override def toString: ConsistencyVarId = name
}

case class ConsistencyUnion(t1: ConsistencyType, t2: ConsistencyType) extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???

    override def toString: ConsistencyVarId = s"(${t1} v $t2)"
}

object ConsistencyTypeLattice {
    private lazy val local: LatticeNode[ConsistencyType] = new LatticeNode(Local, List(strong), List())
    private lazy val strong: LatticeNode[ConsistencyType] = new LatticeNode(Strong, List(weak), List(local))
    private lazy val weak: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(inconsistent), List(strong))
    private lazy val inconsistent: LatticeNode[ConsistencyType] = new LatticeNode(Inconsistent, List(), List(weak))

    def apply(t: ConcreteConsistencyType): LatticeNode[ConsistencyType] = t match {
        case Local => local
        case Strong => strong
        case Weak => weak
        case Inconsistent => inconsistent
    }
}
