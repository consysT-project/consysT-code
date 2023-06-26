package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ClassType

object Natives {
    val objectType: ClassType = types.ClassType("Object", Seq.empty)
    val objectClass: ClassDecl = ClassDecl("Object", Seq.empty, "Object", Map.empty, Map.empty)

    val numberType: ClassType = types.ClassType("Number", Seq.empty)
    val numberClass: ClassDecl = ClassDecl("Number", Seq.empty, "Object", Map.empty, Map.empty)

    val booleanType: ClassType = types.ClassType("Boolean", Seq.empty)
    val booleanClass: ClassDecl = ClassDecl("Boolean", Seq.empty, "Object", Map.empty, Map.empty)

    val unitType: ClassType = types.ClassType("Unit", Seq.empty)
    val unitClass: ClassDecl = ClassDecl("Unit", Seq.empty, "Object", Map.empty, Map.empty)
}
