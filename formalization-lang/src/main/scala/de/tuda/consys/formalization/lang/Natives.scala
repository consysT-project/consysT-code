package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ClassType

object Natives {
    val objectType: ClassType = types.ClassType(topClassId, Seq.empty, Seq.empty)
    val objectClass: ClassDecl = ClassDecl(topClassId, Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    val numberType: ClassType = types.ClassType("Number", Seq.empty, Seq.empty)
    val numberClass: ClassDecl = ClassDecl("Number", Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    val booleanType: ClassType = types.ClassType("Boolean", Seq.empty, Seq.empty)
    val booleanClass: ClassDecl = ClassDecl("Boolean", Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)

    val unitType: ClassType = types.ClassType("Unit", Seq.empty, Seq.empty)
    val unitClass: ClassDecl = ClassDecl("Unit", Seq.empty, Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map.empty, Map.empty)
}
