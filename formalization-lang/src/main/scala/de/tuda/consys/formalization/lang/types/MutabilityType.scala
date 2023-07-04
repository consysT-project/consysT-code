package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.TypeVarEnv

sealed trait MutabilityType extends TypeLike[MutabilityType] {
    def <=(t: MutabilityType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = MutabilityTypeLattice(this).hasUpperBound(t)

    def >=(t: MutabilityType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = MutabilityTypeLattice(this).hasLowerBound(t)

    def lub(t: MutabilityType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): MutabilityType = ???

    def glb(t: MutabilityType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): MutabilityType = ???
}

case object Mutable extends MutabilityType

case object Immutable extends MutabilityType

case object Bottom extends MutabilityType

object MutabilityTypeLattice {
    private lazy val bottom: LatticeNode[MutabilityType] = new LatticeNode(Bottom, List(mutable), Nil)
    private lazy val mutable: LatticeNode[MutabilityType] = new LatticeNode(Mutable, List(immutable), List(bottom))
    private lazy val immutable: LatticeNode[MutabilityType] = new LatticeNode(Immutable, Nil, List(mutable))

    def apply(t: MutabilityType): LatticeNode[MutabilityType] = t match {
        case Bottom => bottom
        case Mutable => mutable
        case Immutable => immutable
    }
}
