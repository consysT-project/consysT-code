package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ConsistencyVarId, TypeVarEnv}

sealed trait ConsistencyType extends TypeLike[ConsistencyType] {
    def operationLevel(): OperationLevel
}

sealed trait ConcreteConsistencyType extends ConsistencyType {
    def <=(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        ConsistencyTypeLattice(this).hasUpperBound(t)

    def >=(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        ConsistencyTypeLattice(this).hasLowerBound(t)

    def lub(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ConsistencyType =
        if (this <= t) t else this // TODO: generalize

    def glb(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ConsistencyType =
        if (this >= t) t else this // TODO: generalize
}

case object Local extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case object Strong extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = StrongOp
}

case object Mixed extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Weak extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Inconsistent extends ConcreteConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case class ConsistencyVar(name: ConsistencyVarId) extends ConsistencyType {
    def <=(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = ???

    def >=(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = ???

    override def lub(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ConsistencyType = ???

    override def glb(t: ConsistencyType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ConsistencyType = ???

    override def operationLevel(): OperationLevel = ???
}

object ConsistencyTypeLattice {
    private lazy val local: LatticeNode[ConsistencyType] = new LatticeNode(Local, List(strong), List())
    private lazy val strong: LatticeNode[ConsistencyType] = new LatticeNode(Strong, List(mixed), List(local))
    private lazy val mixed: LatticeNode[ConsistencyType] = new LatticeNode(Mixed, List(weak), List(strong))
    private lazy val weak: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(inconsistent), List(mixed))
    private lazy val inconsistent: LatticeNode[ConsistencyType] = new LatticeNode(Inconsistent, List(), List(weak))

    def apply(t: ConsistencyType): LatticeNode[ConsistencyType] = t match {
        case Local => local
        case Strong => strong
        case Mixed => mixed
        case Weak => weak
        case Inconsistent => inconsistent
        case ConsistencyVar(_) => sys.error("")
    }
}
