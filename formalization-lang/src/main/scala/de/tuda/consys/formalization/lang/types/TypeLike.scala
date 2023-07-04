package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.TypeVarEnv

trait TypeLike[T] {
    def <=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean

    def !<=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = !this.<=(t)

    def >=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean

    def !>=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = !this.>=(t)

    def lub(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): T

    def glb(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): T
}
