package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, ConsistencyVar, Type, TypeSuffix, TypeSuffixVar}

case class FieldDecl(name: FieldId, typ: Type)

case class VarDecl(name: VarId, typ: Type)

case class TypeVarDecl(name: TypeVarId, upperBound: TypeSuffix)

case class ConsistencyVarDecl(name: ConsistencyVarId, upperBound: ConsistencyType)

case class SuperClassDecl(classId: ClassId, consistencyArgs: Seq[ConsistencyType], typeArgs: Seq[TypeSuffix])

sealed trait MethodDecl {
    def name: MethodId

    def declaredParameters: Seq[VarDecl]

    def declaredParameterTypes: Seq[Type] = declaredParameters.map(param => param.typ)

    def declaredParameterNames: Seq[VarId] = declaredParameters.map(param => param.name)

    def declaredParametersToEnvironment: Map[VarId, Type] = declaredParameters.map(param => param.name -> param.typ).toMap

    def operationLevel: ConsistencyType

    def body: Statement
}

case class QueryMethodDecl(override val name: MethodId,
                           override val operationLevel: ConsistencyType,
                           override val declaredParameters: Seq[VarDecl],
                           returnType: Type,
                           override val body: Statement) extends MethodDecl

case class UpdateMethodDecl(override val name: MethodId,
                            override val operationLevel: ConsistencyType,
                            override val declaredParameters: Seq[VarDecl],
                            override val body: Statement) extends MethodDecl

case class ClassDecl(classId: ClassId,
                     consistencyParameters: Seq[ConsistencyVarDecl],
                     typeParameters: Seq[TypeVarDecl],
                     superClass: SuperClassDecl,
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
            case None if superClass.classId == topClassId => None
            case None => ClassTable.getSuperclass(this).getMethodWithSuperclass(methodId)
        }
    }

    def toType: ClassType =
        ClassType(classId,
            consistencyParameters.map(p => ConsistencyVar(p.name)),
            typeParameters.map(p => TypeSuffixVar(p.name)))

    def typeParametersToEnv: Map[TypeVarId, Type] =
        typeParameters.map(typeVarDecl => typeVarDecl.name -> typeVarDecl.upperBound).toMap
}

case class ProgramDecl(classTable: ClassTable, body: Statement)
