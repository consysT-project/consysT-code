package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ClassType, CompoundClassType, ConsistencyType, OperationLevel, RefType, TerminalType, Types}

import scala.annotation.tailrec

case class UpdateType(operationLevel: OperationLevel, parameters: Seq[TerminalType])

case class QueryType(operationLevel: OperationLevel, parameters: Seq[TerminalType], returnType: TerminalType)

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    def updateType(methodId: MethodId, receiver: TerminalType)(implicit classTable: ClassTable): UpdateType = {
        receiver match {
            case CompoundClassType(classType, consistencyType, mutabilityType) =>
                val classDecl = classTable.getOrElse(classType.classId,
                    sys.error(s"class not found: ${classType.classId}"))
                val mDecl = classDecl.methods.getOrElse(methodId, sys.error(s"method not found"))
                if (mDecl)
            case RefType(classType, consistencyType, mutabilityType) => ???
        }
    }

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
