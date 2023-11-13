package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.Natives.topType
import de.tuda.consys.formalization.lang.types.Types.substitute
import de.tuda.consys.formalization.lang.types._

import scala.annotation.tailrec

sealed trait MethodType

case class UpdateType(operationLevel: ConsistencyType, parameters: Seq[Type], returnType: Type) extends MethodType

case class QueryType(operationLevel: ConsistencyType, parameters: Seq[Type], returnType: Type) extends MethodType

sealed trait MethodBody {
    def operationLevel: ConsistencyType
    def body: Statement
    def arguments: Seq[VarId]
}

case class UpdateBody(override val operationLevel: ConsistencyType,
                      override val body: Statement,
                      override val arguments: Seq[VarId]) extends MethodBody

case class QueryBody(override val operationLevel: ConsistencyType,
                     override val body: Statement,
                     override val arguments: Seq[VarId]) extends MethodBody

object ClassTable {
    type ClassTable = Map[ClassId, ClassDecl]

    def fields(receiver: ClassType)(implicit classTable: ClassTable): Map[FieldId, FieldDecl] = {
        if (receiver == topType)
            return Map.empty

        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"class not found: ${receiver.classId}"))

        val varEnv = (classDecl.typeParameters.map(_.name) zip receiver.typeArguments).toMap
        val consEnv = (classDecl.consistencyParameters.map(_.name) zip receiver.consistencyArguments).toMap

        val inheritedFields = fields(getSuperType(receiver))

        inheritedFields ++ classDecl.fields.values.
          map(f => f.name -> FieldDecl(f.name, substitute(f.typ, varEnv, consEnv), substitute(f.init, varEnv, consEnv))).toMap
    }

    @tailrec
    def mBody(methodId: MethodId, receiver: ClassType)(implicit classTable: ClassTable): MethodBody = {
        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"method $methodId for receiver $receiver not found"))

        val varEnv = (classDecl.typeParameters.map(_.name) zip receiver.typeArguments).toMap
        val consEnv = (classDecl.consistencyParameters.map(_.name) zip receiver.consistencyArguments).toMap

        classDecl.getMethod(methodId) match {
            case Some(value: UpdateMethodDecl) =>
                UpdateBody(substitute(value.operationLevel, consEnv), substitute(value.body, varEnv, consEnv), value.declaredParameterNames)
            case Some(value: QueryMethodDecl) =>
                QueryBody(substitute(value.operationLevel, consEnv), substitute(value.body, varEnv, consEnv), value.declaredParameterNames)
            case None => mBody(methodId, getSuperType(receiver))
        }
    }

    @tailrec
    def mType(methodId: MethodId, receiver: ClassType)(implicit classTable: ClassTable): MethodType = {
        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"method $methodId for receiver $receiver not found"))

        val varEnv = (classDecl.typeParameters.map(_.name) zip receiver.typeArguments).toMap
        val consEnv = (classDecl.consistencyParameters.map(_.name) zip receiver.consistencyArguments).toMap

        classDecl.getMethod(methodId) match {
            case Some(u@UpdateMethodDecl(_, operationLevel, declaredParameters, _)) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv, consEnv))
                val concreteReturnType = substitute(u.returnType, varEnv, consEnv)
                UpdateType(substitute(operationLevel, consEnv), concreteParams, concreteReturnType)
            case Some(QueryMethodDecl(_, operationLevel, declaredParameters, returnType, _)) =>
                val concreteParams = declaredParameters.map(p => substitute(p.typ, varEnv, consEnv))
                val concreteReturnType = substitute(returnType, varEnv, consEnv)
                QueryType(substitute(operationLevel, consEnv), concreteParams, concreteReturnType)
            case None => mType(methodId, getSuperType(receiver))
        }
    }

    @tailrec
    def recvDecl(methodId: MethodId, receiver: ClassType)(implicit classTable: ClassTable): ClassType = {
        val classDecl = classTable.getOrElse(receiver.classId,
            sys.error(s"method $methodId for receiver $receiver not found"))

        classDecl.methods.get(methodId) match {
            case Some(_) => receiver
            case None => recvDecl(methodId, getSuperType(receiver))
        }
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
