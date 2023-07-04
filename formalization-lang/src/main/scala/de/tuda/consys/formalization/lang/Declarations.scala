package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.types.{ClassType, OperationLevel, Type}

case class FieldDecl(name: FieldId, typ: Type)

case class VarDecl(name: VarId, typ: Type)

case class TypeVarDecl(name: TypeVarId, upperBound: Type)

sealed trait MethodDecl {
    def name: MethodId

    def declaredParameters: Seq[VarDecl]

    def declaredParameterTypes: Seq[Type] = declaredParameters.map(param => param.typ)

    def declaredParameterNames: Seq[VarId] = declaredParameters.map(param => param.name)

    def operationLevel: OperationLevel

    def body: IRExpr
}

case class QueryMethodDecl(override val name: MethodId,
                           override val operationLevel: OperationLevel,
                           override val declaredParameters: Seq[VarDecl],
                           returnType: Type,
                           override val body: IRExpr) extends MethodDecl

case class UpdateMethodDecl(override val name: MethodId,
                            override val operationLevel: OperationLevel,
                            override val declaredParameters: Seq[VarDecl],
                            override val body: IRExpr) extends MethodDecl

case class ClassDecl(classId: ClassId,
                     typeParameters: Seq[TypeVarDecl],
                     superClass: (ClassId, Seq[Type]),
                     fields: Map[FieldId, FieldDecl],
                     methods: Map[MethodId, MethodDecl]) {

    def getField(fieldId: FieldId): Option[FieldDecl] =
        fields.get(fieldId)

    def getMethod(methodId: MethodId): Option[MethodDecl] =
        methods.get(methodId)

    def getMethodWithSuperclass(methodId: MethodId)
                               (implicit classTable: ClassTable): Option[MethodDecl] = {
        getMethod(methodId) match {
            case v@Some(_) => v
            case None if superClass._1 == topClassId => None
            case None => ClassTable.getSuperclass(classId).getMethodWithSuperclass(methodId)
        }
    }

    def toType: ClassType =
        types.ClassType(classId, typeParameters.map(p => p.upperBound))

    def toConcreteType(typeArgs: Seq[Type])(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ClassType = {
        require(typeArgs.length == typeParameters.length)
        require((typeArgs zip typeParameters).forall(e => e._1 <= e._2.upperBound))
        types.ClassType(classId, typeArgs)
    }

    def typeParametersToEnv: Map[TypeVarId, Type] =
        typeParameters.map(typeVarDecl => typeVarDecl.name -> typeVarDecl.upperBound).toMap

    def superClassType: ClassType =
        types.ClassType(superClass._1, superClass._2)
}

case class ProgramDecl(classTable: ClassTable, body: IRExpr)
