package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.types.{ConsistencyType, Type}

package object lang {
    type ClassId = String

    type FieldId = String

    type MethodId = String

    type VarId = String

    type TypeVarId = String

    type ConsistencyVarId = String

    type TypeVarEnv = Map[TypeVarId, Type]

    type ConsistencyVarEnv = Map[ConsistencyVarId, ConsistencyType]

    val thisId = "this"

    val topClassId = "Object"
}
