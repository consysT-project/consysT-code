package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.types2.{ConsistencyType, MutabilityType, TypeSuffix}

package object lang {
    type ClassId = String

    type FieldId = String

    type MethodId = String

    type VarId = String

    type TypeVarId = String

    type ConsistencyVarId = String

    type TypeVarEnv = Map[TypeVarId, TypeSuffix]

    type TypeVarMutabilityEnv = Map[TypeVarId, MutabilityType]

    type ConsistencyVarEnv = Map[ConsistencyVarId, ConsistencyType]

    val thisId = "this"

    val topClassId = "Object"
}
