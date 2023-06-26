package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.types.ConsistencyType

package object lang {
    type ClassId = String

    type FieldId = String

    type MethodId = String

    type VarId = String

    type TypeVarId = String

    type ClassTable = Map[(ClassId, ConsistencyType), ClassDecl]

    val thisId = "this"
}
