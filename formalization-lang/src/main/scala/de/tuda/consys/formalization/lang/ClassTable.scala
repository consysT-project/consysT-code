package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.errors.ExecutionError
import de.tuda.consys.formalization.lang.types.Types.substitute
import de.tuda.consys.formalization.lang.types._

import scala.annotation.tailrec

sealed trait MethodType

case class UpdateType(operationLevel: ConsistencyType, parameters: Seq[Type]) extends MethodType

case class QueryType(operationLevel: ConsistencyType, parameters: Seq[Type], returnType: Type) extends MethodType

case class MethodBody(operationLevel: ConsistencyType, body: Statement, arguments: Seq[VarId])

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    @tailrec
    def mBody(methodId: MethodId, receiver: ClassType)(implicit classTable: ClassTable): MethodBody = {
        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"class not found: ${receiver.classId}"))

        val consEnv = (classDecl.consistencyParameters.map(_.name) zip receiver.consistencyArguments).toMap

        classDecl.methods.get(methodId) match {
            case Some(value) => MethodBody(substitute(value.operationLevel, consEnv), value.body, value.declaredParameterNames)
            case None => mBody(methodId, getSuperType(receiver))
        }
    }

    def fields(receiver: ClassType)(implicit classTable: ClassTable): Map[FieldId, FieldDecl] = {
        if (receiver.classId == topClassId)
            return Map.empty

        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"class not found: ${receiver.classId}"))
        val varEnv = (classDecl.typeParameters.map(_.name) zip receiver.typeArguments).toMap
        val consEnv = (classDecl.consistencyParameters.map(_.name) zip receiver.consistencyArguments).toMap

        val supertype = substitute(getSuperclass(classDecl).toType, varEnv, consEnv)
        val inheritedFields = fields(supertype)

        inheritedFields ++ classDecl.fields.values.
            map(f => f.name -> FieldDecl(f.name, substitute(f.typ, varEnv, consEnv))).toMap
    }

    def mType(methodId: MethodId, receiver: ClassType)(implicit classTable: ClassTable): MethodType = {
        val classType = receiver

        val classDecl = classTable.getOrElse(classType.classId,
            sys.error(s"class not found: ${classType.classId}"))
        val mDecl = classDecl.methods.getOrElse(methodId,
            sys.error(s"method not found"))
        if (classDecl.typeParameters.length != classType.typeArguments.length)
            sys.error(s"wrong number of type arguments: $receiver")
        val varEnv = (classDecl.typeParameters.map(_.name) zip classType.typeArguments).toMap
        val consEnv = (classDecl.consistencyParameters.map(_.name) zip classType.consistencyArguments).toMap

        mDecl match {
            case UpdateMethodDecl(_, operationLevel, declaredParameters, _) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv, consEnv))
                UpdateType(substitute(operationLevel, consEnv), concreteParams)

            case QueryMethodDecl(_, operationLevel, declaredParameters, returnType, _) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv, consEnv))
                val concreteReturnType = substitute(returnType, varEnv, consEnv)
                QueryType(substitute(operationLevel, consEnv), concreteParams, concreteReturnType)
        }
    }

    def recvDecl(methodId: MethodId, receiver: ClassType): ClassType = ???

    def getSuperclass(classDecl: ClassDecl)(implicit classTable: ClassTable): ClassDecl = {
        classTable.getOrElse(classDecl.superClass.classId,
            sys.error(s"superclass not found: ${classDecl.superClass.classId}"))
    }

    def getSuperType(classType: ClassType)(implicit classTable: ClassTable): ClassType = {
        val subClass = classTable.getOrElse(classType.classId,
            sys.error(s"class not found: ${classType.classId}"))

        val typeVars = subClass.typeParameters.map(d => d.name -> d.upperBound).toMap
        val consistencyVars = subClass.consistencyParameters.map(d => d.name -> d.upperBound).toMap

        val l2 = subClass.superClass.consistencyArgs.map(p => substitute(p, consistencyVars))
        val t2 = subClass.superClass.typeArgs.map(p => substitute(p, typeVars, consistencyVars))

        ClassType(subClass.superClass.classId, l2, t2)
    }
}
