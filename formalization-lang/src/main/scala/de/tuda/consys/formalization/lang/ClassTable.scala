package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ConsistencyType

import scala.annotation.tailrec

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    @tailrec
    def isSuperclass(subclassId: ClassId, superclassId: ClassId)(implicit classTable: ClassTable): Boolean = {
        if (superclassId == topClassId)
            return true

        (findDeclaration(subclassId), findDeclaration(superclassId)) match {
            case (Some(subclass), Some(_)) =>
                subclass.superClass._1 == superclassId || isSuperclass(subclass.superClass._1, superclassId)
            case (Some(_), _) => sys.error(s"class not found: $superclassId")
            case _ => sys.error(s"class not found: $subclassId")
        }
    }

    def findDeclaration(id: ClassId)(implicit classTable: ClassTable): Option[ClassDecl] =
        classTable.get(id)

    def getSuperclass(id: ClassId)(implicit classTable: ClassTable): ClassDecl =
        findDeclaration(id) match {
            case Some(value) => findDeclaration(value.classId) match {
                case Some(value) => value
                case None => sys.error(s"class not found: $value")
            }
            case None => sys.error(s"class not found: $id")
        }
}
