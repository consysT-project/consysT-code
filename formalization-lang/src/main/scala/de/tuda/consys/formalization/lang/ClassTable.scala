package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, Types}

import scala.annotation.tailrec

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    // TODO: do we need to consider the type-var environment here?
    private def getSuperType(classType: ClassType)(implicit classTable: ClassTable): ClassType = {
        val subClass = classTable.getOrElse(classType.classId, sys.error(s"class not found: ${classType.classId}"))

        val typeVars = subClass.typeParameters.map(d => d.name -> d.upperBound).toMap
        val t2 = subClass.superClass._2.map(p => Types.substitute(p, typeVars))

        ClassType(subClass.superClass._1, classType.consistencyArguments, t2)
    }

    private def isDirectSuperclass(subclass: ClassType, superclass: ClassType)(implicit classTable: ClassTable): Boolean = {
        superclass.classId == topClassId || // S-Top
            subclass == superclass || // S-Refl
            getSuperType(subclass) == superclass // S-Cls
    }

    @tailrec
    def isSuperClassType(subclass: ClassType, superclass: ClassType)(implicit classTable: ClassTable): Boolean =
        isDirectSuperclass(subclass, superclass) || isSuperClassType(getSuperType(subclass), superclass)
}
