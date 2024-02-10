package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, ConsistencyVar, Immutable, Local, LocalTypeSuffix, MutabilityType, Type, TypeSuffix, TypeSuffixVar, UnitTypeSuffix}

case class FieldDecl(name: FieldId, typ: Type, init: Expression)

case class VarDecl(name: VarId, typ: Type)

case class TypeVarDecl(name: TypeVarId, upperBound: TypeSuffix, mBound: MutabilityType)

case class ConsistencyVarDecl(name: ConsistencyVarId, upperBound: ConsistencyType)

case class SuperClassDecl(classId: ClassId, consistencyArgs: Seq[ConsistencyType], typeArgs: Seq[TypeSuffix]) {
    def toClassType: ClassType = ClassType(classId, consistencyArgs, typeArgs)
}

sealed trait MethodDecl {
    def name: MethodId

    def declaredParameters: Seq[VarDecl]

    def declaredParameterTypes: Seq[Type] = declaredParameters.map(param => param.typ)

    def declaredParameterNames: Seq[VarId] = declaredParameters.map(param => param.name)

    def declaredParametersToEnvironment: Map[VarId, Type] = declaredParameters.map(param => param.name -> param.typ).toMap

    def operationLevel: ConsistencyType

    def returnType: Type

    def body: Statement
}

case class QueryMethodDecl(override val name: MethodId,
                           override val operationLevel: ConsistencyType,
                           override val declaredParameters: Seq[VarDecl],
                           override val returnType: Type,
                           override val body: Statement) extends MethodDecl

case class UpdateMethodDecl(override val name: MethodId,
                            override val operationLevel: ConsistencyType,
                            override val declaredParameters: Seq[VarDecl],
                            override val body: Statement) extends MethodDecl {
    override def returnType: Type = Type(Local, Immutable, UnitTypeSuffix)
}

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

    def toType: ClassType =
        ClassType(classId,
            consistencyParameters.map(p => ConsistencyVar(p.name)),
            typeParameters.map(p => TypeSuffixVar(p.name)))

    def typeParametersToEnv: TypeVarEnv =
        typeParameters.map(typeVarDecl => typeVarDecl.name -> typeVarDecl.upperBound).toMap

    def typeParameterMutabilityBoundsToEnv: TypeVarMutabilityEnv =
        typeParameters.map(p => p.name -> p.mBound).toMap

    def consistencyParametersToEnv: ConsistencyVarEnv =
        consistencyParameters.map(consistencyVarEnv => consistencyVarEnv.name -> consistencyVarEnv.upperBound).toMap
}

case class ProgramDecl(classTable: ClassTable, processes: Array[Statement])
