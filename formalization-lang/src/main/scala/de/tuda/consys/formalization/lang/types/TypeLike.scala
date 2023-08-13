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

trait TypeLike2[T, T2] {
    def <=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): Boolean

    def !<=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): Boolean = !this.<=(t)

    def >=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): Boolean

    def !>=(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): Boolean = !this.>=(t)

    def lub(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): T

    def glb(t: T)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: T2): T
}
