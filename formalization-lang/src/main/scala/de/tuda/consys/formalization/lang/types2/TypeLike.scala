package de.tuda.consys.formalization.lang.types2

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ConsistencyVarEnv, TypeVarEnv}

trait TypeLike[T] {
    def <=(t: T)(implicit classTable: ClassTable,
                 typeVarEnv: TypeVarEnv,
                 consistencyVarEnv: ConsistencyVarEnv): Boolean

    def !<=(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  consistencyVarEnv: ConsistencyVarEnv): Boolean = !this.<=(t)

    def >=(t: T)(implicit classTable: ClassTable,
                 typeVarEnv: TypeVarEnv,
                 consistencyVarEnv: ConsistencyVarEnv): Boolean

    def !>=(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  consistencyVarEnv: ConsistencyVarEnv): Boolean = !this.>=(t)

    def lub(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  consistencyVarEnv: ConsistencyVarEnv): T

    def glb(t: T)(implicit classTable: ClassTable,
                  typeVarEnv: TypeVarEnv,
                  consistencyVarEnv: ConsistencyVarEnv): T
}
