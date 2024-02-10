package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ConsistencyVarEnv, TypeVarEnv, TypeVarMutabilityEnv}

trait TypeLike[T] {
    def <=(t: T)(implicit classTable: ClassTable,
                 typeVarEnv: TypeVarEnv,
                 typeVarMutabilityEnv: TypeVarMutabilityEnv,
                 consistencyVarEnv: ConsistencyVarEnv): Boolean

    def !<=(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  typeVarMutabilityEnv: TypeVarMutabilityEnv,
                  consistencyVarEnv: ConsistencyVarEnv): Boolean = !this.<=(t)

    def >=(t: T)(implicit classTable: ClassTable,
                 typeVarEnv: TypeVarEnv,
                 typeVarMutabilityEnv: TypeVarMutabilityEnv,
                 consistencyVarEnv: ConsistencyVarEnv): Boolean

    def !>=(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  typeVarMutabilityEnv: TypeVarMutabilityEnv,
                  consistencyVarEnv: ConsistencyVarEnv): Boolean = !this.>=(t)
}
