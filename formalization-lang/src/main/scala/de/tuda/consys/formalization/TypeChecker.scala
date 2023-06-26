package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._

// TODO: resolve class type arguments correctly
// TODO: check transactions
// TODO: check invalid identifier 'this' (since we don't have a parser yet)
object TypeChecker {
    case class TypeError(message: String) extends Exception(message)

    private sealed trait MethodMutabilityContext

    private case object ImmutableContext extends MethodMutabilityContext

    private case object MutableContext extends MethodMutabilityContext

    private sealed trait DeclarationContext

    private case object TopLevelContext extends DeclarationContext

    private case class MethodContext(thisType: (ClassType, ConsistencyType),
                                     mutabilityContext: MethodMutabilityContext,
                                     operationLevel: OperationLevel) extends DeclarationContext

    private type VarEnv = Map[VarId, Type]

    private type TypeVarEnv = Map[TypeVarId, Type]

    def checkProgram(programDecl: ProgramDecl): Unit = {
        programDecl.classTable.foreachEntry((c, decl) => checkClass(decl, c._2)(programDecl.classTable))

        typeOfExpr(programDecl.body, Map.empty, Map.empty)(TopLevelContext, Local, programDecl.classTable)
    }

    private def checkClass(classDecl: ClassDecl, thisConsistency: ConsistencyType)(implicit classTable: ClassTable): Unit = {
        classDecl.methods.foreachEntry((methodId, methodDecl) => {
            val varEnv: VarEnv = methodDecl.declaredParameters.map(varDecl => varDecl.name -> varDecl.typ).toMap
            val typeVarEnv: TypeVarEnv = classDecl.typeParametersToEnv

            methodDecl match {
                case QueryMethodDecl(_, operationLevel, _, declaredReturnType, body) =>
                    val returnType = resolveType(
                        typeOfExpr(body, varEnv, typeVarEnv)(MethodContext((classDecl.toType, thisConsistency), ImmutableContext, operationLevel), Local, classTable),
                        typeVarEnv)
                    val resolvedDeclaredReturnType = resolveType(declaredReturnType, typeVarEnv)

                    if (returnType !<= resolvedDeclaredReturnType)
                        throw TypeError(s"return type is wrong. Expected: $resolvedDeclaredReturnType, but was $returnType (in method ${classDecl.classId}.$methodId})")

                case UpdateMethodDecl(_, operationLevel, _, body) =>
                    val returnType = resolveType(
                        typeOfExpr(body, varEnv, typeVarEnv)(MethodContext((classDecl.toType, thisConsistency), MutableContext, operationLevel), Local, classTable),
                        typeVarEnv)

                    if (returnType.classType != Natives.unitType)
                        throw TypeError(s"return type is wrong. Expected: $Natives.UnitType, but was $returnType (in method $methodId)")
            }
        })
    }

    private def typeOfExpr(expr: IRExpr, vars: VarEnv, typeVars: TypeVarEnv)(implicit declarationContext: DeclarationContext,
                                                       implicitContext: ConsistencyType,
                                                       classTable: ClassTable): Type = expr match {
        case True => CompoundType(Natives.booleanType, Local, Bottom)
        case False => CompoundType(Natives.booleanType, Local, Bottom)
        case UnitLiteral => CompoundType(Natives.unitType, Local, Bottom)
        case Num(_) => CompoundType(Natives.numberType, Local, Bottom)

        case Var(id: VarId) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case Let(id: VarId, namedExpr: IRExpr, body: IRExpr) =>
            val namedType = typeOfExpr(namedExpr, vars, typeVars)
            typeOfExpr(body, vars + (id -> namedType), typeVars)

        case If(conditionExpr, thenExpr, elseExpr) =>
            val condType = resolveType(typeOfExpr(conditionExpr, vars, typeVars), typeVars)

            if (condType.classType != Natives.booleanType)
                throw TypeError(s"condition must be Bool, but was: $condType")

            val newImplicitContext = implicitContext glb condType.consistencyType

            val t1 = typeOfExpr(thenExpr, vars, typeVars)(declarationContext, newImplicitContext, classTable)
            val t2 = typeOfExpr(elseExpr, vars, typeVars)(declarationContext, newImplicitContext, classTable)

            if (t1 != t2) // TODO: use lub for expression type inference instead?
                throw TypeError(s"branches have diverging types: $t1 and $t2")

            t1

        case Equals(expr1, expr2) =>
            val t1 = resolveType(typeOfExpr(expr1, vars, typeVars), typeVars)
            val t2 = resolveType(typeOfExpr(expr2, vars, typeVars), typeVars)

            if (t1.classType != t2.classType)
                throw TypeError(s"non-matching types in <Equals>: $t1 and $t2")

            CompoundType(Natives.booleanType, t1.consistencyType lub t2.consistencyType, Mutable) // TODO: mutability type

        case Add(expr1, expr2) =>
            val t1 = resolveType(typeOfExpr(expr1, vars, typeVars), typeVars)
            val t2 = resolveType(typeOfExpr(expr2, vars, typeVars), typeVars)

            if (t1.classType != Natives.numberType || t2.classType != Natives.numberType)
                throw TypeError(s"invalid types for <Add>: $t1 and $t2")

            CompoundType(Natives.numberType, t1.consistencyType lub t2.consistencyType, Mutable) // TODO: mutability type

        case This =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside of class declaration")

                case MethodContext((classType, consistencyType), _, _) =>
                    CompoundType(classType, consistencyType, Mutable)
            }

        case GetField(fieldId: FieldId) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside of class declaration")

                case MethodContext(thisType, _, operationLevel) =>
                    val classDecl = classTable
                        .getOrElse((thisType._1.classId, thisType._2), throw TypeError(s"class of 'this' not available: $thisType"))

                    val fieldDecl = classDecl.getField(fieldId).
                        getOrElse(throw TypeError(s"field not available: $fieldId (in class ${thisType._1.classId})"))

                    val fieldType = resolveType(fieldDecl.typ, classDecl.typeParametersToEnv)

                    CompoundType(fieldType.classType, fieldType.consistencyType lub operationLevel.consistencyType(), fieldType.mutabilityType)
            }

        case SetField(fieldId: FieldId, value: IRExpr) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (mutabilityContext != MutableContext)
                        throw TypeError("assignment in immutable context: " + thisType)

                    val valueType = resolveType(typeOfExpr(value, vars, typeVars), typeVars)

                    val classDecl = classTable.getOrElse((thisType._1.classId, thisType._2), throw TypeError(s"class of 'this' not available: $thisType"))
                    val fieldDecl = classDecl.getField(fieldId).getOrElse(throw TypeError(s"field not available: $fieldId (in class $thisType)"))
                    val fieldType = resolveType(fieldDecl.typ, classDecl.typeParametersToEnv)

                    if (valueType !<= fieldType)
                        throw TypeError(s"assignment has wrong type. expected: $fieldType (but was: $valueType)")

                    // TODO: should we separate immutable types from field mutability through assignment?
                    //if (fieldType.mutabilityType == Immutable)
                    //    throw TypeError(s"wrong assignment of immutable field")

                    if (implicitContext !<= fieldType.consistencyType)
                        throw TypeError(s"wrong assignment in implicit context: ${fieldDecl.typ} in $implicitContext context")

                    if (operationLevel.consistencyType() !<= fieldType.consistencyType)
                        throw TypeError(s"wrong assignment in operation context: ${fieldDecl.typ} in ${operationLevel.consistencyType()} context")

                    valueType
            }

        case CallQuery(recv, methodId, arguments) =>
            val recvType = resolveType(typeOfExpr(recv, vars, typeVars), typeVars)
            val argTypes = arguments.map(argExpr => resolveType(typeOfExpr(argExpr, vars, typeVars), typeVars))

            val (methodDecl, recvTypeEnv) = checkMethodCall(recvType, methodId, argTypes)

            val queryDecl = methodDecl match {
                case q: QueryMethodDecl => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            resolveType(queryDecl.returnType, recvTypeEnv)

        case CallUpdate(recv, methodId, arguments) =>
            val recvType = resolveType(typeOfExpr(recv, vars, typeVars), typeVars)

            if (recvType.mutabilityType == Immutable)
                throw TypeError(s"invalid update call on immutable receiver: $methodId (in class ${recvType.classType.classId})")

            val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars, typeVars))
            val (methodDecl, _) = checkMethodCall(recvType, methodId, argTypes)

            if (!(implicitContext <= methodDecl.operationLevel.consistencyType()))
                throw TypeError(s"wrong operation level in context: ${methodDecl.operationLevel.consistencyType()} in $implicitContext")

            methodDecl match {
                case _: UpdateMethodDecl =>
                case _ => throw TypeError(s"expected update method: $methodId")
            }

            CompoundType(Natives.unitType, Local, Bottom)

        case Sequence(exprs) =>
            exprs.foldLeft(null: Type)((r, e) => typeOfExpr(e, vars, typeVars))

        case Transaction(body) =>
            typeOfExpr(body, vars, typeVars)

        case New(_, classId, typeArgs, consistencyType, args) =>
            val classDecl = classTable.getOrElse((classId, consistencyType), throw TypeError(s"class not available: $consistencyType $classId"))

            if (typeArgs.length != classDecl.typeParameters.length)
                throw TypeError(s"wrong number of type arguments: $classId")

            val classVarEnv = classDecl.typeParameters.map(p => p.name -> p.upperBound).toMap

            (typeArgs zip classDecl.typeParameters).foreach(e => {
                val (arg, paramDecl) = e
                val paramBound = resolveType(TypeVar(paramDecl.name), classVarEnv)
                if (arg !<= paramBound)
                    throw TypeError(s"wrong type argument for type variable: $arg (expected: $paramDecl)")
            })

            if (args.size != classDecl.fields.size)
                throw TypeError(s"wrong number of constructor arguments: $classId")

            args.foreachEntry((fieldId, expr) => {
                val argType = resolveType(typeOfExpr(expr, vars, typeVars), typeVars)
                val field = classDecl.fields.getOrElse(fieldId,
                    throw TypeError(s"field not found in constructor: $fieldId (in class $classId)"))
                val fieldType = resolveType(field.typ, classVarEnv)

                if (argType !<= fieldType)
                    throw TypeError(s"wrong constructor argument type: expected $fieldType, but was $argType (in class $classId)")
            })

            CompoundType(types.ClassType(classId, typeArgs), consistencyType, Mutable) // TODO: which mutability type here?

        case _ => ???
    }

    private def checkMethodCall(recvType: CompoundType, methodId: MethodId, argTypes: Seq[Type])
                               (implicit declarationContext: DeclarationContext,
                                implicitContext: ConsistencyType,
                                classTable: ClassTable): (MethodDecl, TypeVarEnv) = {
        val recvClassDecl = classTable.getOrElse((recvType.classType.classId, recvType.consistencyType), throw TypeError(s"class not available: $recvType"))

        if (recvClassDecl.typeParameters.length != recvType.classType.typeArguments.length)
            throw TypeError(s"wrong number of type arguments: $recvType")

        val typeEnv: TypeVarEnv =
            (recvClassDecl.typeParameters zip recvType.classType.typeArguments).map(p => (p._1.name, p._2)).toMap

        val methodDecl: MethodDecl = recvClassDecl.getMethod(methodId)
            .getOrElse(throw TypeError(s"method not available: $methodId (in class ${recvType.classType.classId})"))

        if (argTypes.size != methodDecl.declaredParameters.size)
            throw TypeError(s"wrong number of arguments for method $methodId: ${argTypes.size} (expected: ${methodDecl.declaredParameters.size}")

        (argTypes zip methodDecl.declaredParameterTypes).foreach(t => {
            val argType = t._1
            val parameterType = resolveType(t._2, typeEnv)
            if (!(argType <= parameterType))
                throw TypeError(s"wrong argument type for method $methodId: $argType (expected: $parameterType)")
        })

        (methodDecl, typeEnv)
    }

    private def resolveType(typ: Type, typeVars: TypeVarEnv): CompoundType = typ match {
        case TypeVar(name) =>
            val r = typeVars.getOrElse(name, throw TypeError(s"cannot resolve type variable <$name>"))
            resolveType(r, typeVars)

        case CompoundType(ClassType(classId, typeArgs), c, m) =>
            CompoundType(types.ClassType(classId, typeArgs.map(typeArg => resolveType(typeArg, typeVars))), c, m)
    }
}
