package de.tuda.consys.formalization.lang

case class FieldDecl(name: FieldId, typ: Type)

case class VarDecl(name: VarId, typ: Type)

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
                     typeParameters: Seq[TypeVar],
                     fields: Map[FieldId, FieldDecl],
                     methods: Map[MethodId, MethodDecl]) {

    def getField(fieldId: FieldId): Option[FieldDecl] =
        fields.get(fieldId)

    def getMethod(methodId: MethodId): Option[MethodDecl] =
        methods.get(methodId)

    def toType: ClassType =
        ClassType(classId, typeParameters)

    def toConcreteType(typeArgs: Seq[Type]): ClassType = {
        require(typeArgs.length == typeParameters.length)
        ClassType(classId, typeArgs)
    }

    def typeParametersMapTo[A](others: Seq[A]): Map[TypeVarId, A] =
        typeParameters.map(typeVar => typeVar.typeVarId).zip(others).toMap
}

case class ProgramDecl(classTable: ClassTable, body: IRExpr)
