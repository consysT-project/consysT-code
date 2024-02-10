package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.types.{ConsistencyType, MutabilityType, TypeSuffix}

package object lang {
    type NumericType = Int

    type ClassId = String

    type FieldId = String

    type MethodId = String

    type VarId = String

    type TypeVarId = String

    type ConsistencyVarId = String

    type TypeVarEnv = Map[TypeVarId, TypeSuffix]

    type TypeVarMutabilityEnv = Map[TypeVarId, MutabilityType]

    type ConsistencyVarEnv = Map[ConsistencyVarId, ConsistencyType]

    val thisId: VarId = "this"

    val resId: VarId = "res"

    val topClassId = "Object"
}
