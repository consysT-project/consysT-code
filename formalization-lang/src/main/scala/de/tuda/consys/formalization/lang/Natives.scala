package de.tuda.consys.formalization.lang

object Natives {
    val numberType: ClassType = ClassType("Number", Seq.empty)
    val numberClass: ClassDecl = ClassDecl("Number", Seq.empty, Map.empty, Map.empty)

    val booleanType: ClassType = ClassType("Boolean", Seq.empty)
    val booleanClass: ClassDecl = ClassDecl("Boolean", Seq.empty, Map.empty, Map.empty)

    val unitType: ClassType = ClassType("Unit", Seq.empty)
    val unitClass: ClassDecl = ClassDecl("Unit", Seq.empty, Map.empty, Map.empty)
}
