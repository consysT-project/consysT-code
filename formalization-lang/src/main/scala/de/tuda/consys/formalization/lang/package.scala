package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.types.Type

package object lang {
    type ClassId = String

    type FieldId = String

    type MethodId = String

    type VarId = String

    type TypeVarId = String

    type TypeVarEnv = Map[TypeVarId, Type]

    val thisId = "this"

    val topClassId = "Object"
}
