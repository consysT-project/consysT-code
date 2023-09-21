package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ConsistencyVarEnv, TypeVarEnv}

sealed trait MutabilityType extends TypeLike[MutabilityType] {
    def <=(t: MutabilityType)(implicit classTable: ClassTable,
                              typeVarEnv: TypeVarEnv,
                              consistencyVarEnv: ConsistencyVarEnv): Boolean =
        Subtyping.subtype(this, t)

    def >=(t: MutabilityType)(implicit classTable: ClassTable,
                              typeVarEnv: TypeVarEnv,
                              consistencyVarEnv: ConsistencyVarEnv): Boolean =
        Subtyping.subtype(t, this)

    def lub(t: MutabilityType)(implicit classTable: ClassTable,
                               typeVarEnv: TypeVarEnv,
                               consistencyVarEnv: ConsistencyVarEnv): MutabilityType =
        if (this <= t) t else this // TODO: generalize

    def glb(t: MutabilityType)(implicit classTable: ClassTable,
                               typeVarEnv: TypeVarEnv,
                               consistencyVarEnv: ConsistencyVarEnv): MutabilityType =
        if (this >= t) t else this // TODO: generalize
}

case object Mutable extends MutabilityType

case object Immutable extends MutabilityType

object MutabilityTypeLattice {
    private lazy val mutable: LatticeNode[MutabilityType] = new LatticeNode(Mutable, List(immutable), Nil)
    private lazy val immutable: LatticeNode[MutabilityType] = new LatticeNode(Immutable, Nil, List(mutable))

    def apply(t: MutabilityType): LatticeNode[MutabilityType] = t match {
        case Mutable => mutable
        case Immutable => immutable
    }
}
