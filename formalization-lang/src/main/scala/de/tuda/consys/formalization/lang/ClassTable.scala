package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.Types.substitute
import de.tuda.consys.formalization.lang.types._

import scala.annotation.tailrec

sealed trait MethodType

case class UpdateType(operationLevel: OperationLevel, parameters: Seq[Type]) extends MethodType

case class QueryType(operationLevel: OperationLevel, parameters: Seq[Type], returnType: Type) extends MethodType

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    def mType(methodId: MethodId, receiver: TerminalType)(implicit classTable: ClassTable): MethodType = {
        val classType = receiver.classType

        val classDecl = classTable.getOrElse(classType.classId,
            sys.error(s"class not found: ${classType.classId}"))
        val mDecl = classDecl.methods.getOrElse(methodId,
            sys.error(s"method not found"))
        if (classDecl.typeParameters.length != classType.typeArguments.length)
            sys.error(s"wrong number of type arguments: $receiver")
        val varEnv = (classDecl.typeParameters.map(_.name) zip classType.typeArguments).toMap

        mDecl match {
            case UpdateMethodDecl(_, operationLevel, declaredParameters, _) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv))
                UpdateType(operationLevel, concreteParams)

            case QueryMethodDecl(_, operationLevel, declaredParameters, _, _, returnType) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv))
                val concreteReturnType = substitute(returnType, varEnv)
                QueryType(operationLevel, concreteParams, concreteReturnType)
        }
    }

    def getSuperclass(classDecl: ClassDecl)(implicit classTable: ClassTable): ClassDecl = {
        classTable.getOrElse(classDecl.superClass.classId,
            sys.error(s"superclass not found: ${classDecl.superClass.classId}"))
    }

    // TODO: do we need to consider the type-var environment here?
    private def getSuperType(classType: ClassType)(implicit classTable: ClassTable): ClassType = {
        val subClass = classTable.getOrElse(classType.classId,
            sys.error(s"class not found: ${classType.classId}"))

        val typeVars = subClass.typeParameters.map(d => d.name -> d.upperBound).toMap
        val t2 = subClass.superClass.typeArgs.map(p => substitute(p, typeVars))

        val consistencyVars = subClass.consistencyParameters.map(d => d.name -> d.upperBound).toMap
        val l2 = subClass.superClass.consistencyArgs.map(p => substitute(p, consistencyVars))

        ClassType(subClass.superClass.classId, classType.consistencyArguments, t2)
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
