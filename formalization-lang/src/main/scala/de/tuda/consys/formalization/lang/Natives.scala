package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ClassType

object Natives {
    val objectType: ClassType = types.ClassType(topClassId, Seq.empty, Seq.empty)

    private val numberClassId = "Number"
    val numberType: ClassType = types.ClassType(numberClassId, Seq.empty, Seq.empty)
    val numberClass: ClassDecl = ClassDecl(numberClassId, Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    private val booleanClassId = "Boolean"
    val booleanType: ClassType = types.ClassType(booleanClassId, Seq.empty, Seq.empty)
    val booleanClass: ClassDecl = ClassDecl(booleanClassId, Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    private val unitClassId = "Unit"
    val unitType: ClassType = types.ClassType(unitClassId, Seq.empty, Seq.empty)
    val unitClass: ClassDecl = ClassDecl(unitClassId, Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    val natives: Set[ClassId] = Set(numberClassId, booleanClassId, unitClassId)
}
