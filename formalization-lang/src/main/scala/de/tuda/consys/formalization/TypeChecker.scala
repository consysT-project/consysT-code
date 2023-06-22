package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang._

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

        typeOfExpr(programDecl.body, Map.empty)(TopLevelContext, Local, programDecl.classTable)
    }

    private def checkClass(classDecl: ClassDecl, thisConsistency: ConsistencyType)(implicit classTable: ClassTable): Unit = {
        classDecl.methods.foreachEntry((methodId, methodDecl) => {
            val varEnv: VarEnv = methodDecl.declaredParameters.map(varDecl => varDecl.name -> varDecl.typ).toMap
            methodDecl match {
                case QueryMethodDecl(_, operationLevel, _, declaredReturnType, body) =>
                    val returnType = typeOfExpr(body, varEnv)(MethodContext((classDecl.toType, thisConsistency), ImmutableContext, operationLevel), Local, classTable).effectiveType()
                    if (!(returnType <= declaredReturnType))
                        throw TypeError(s"return type is wrong. Expected: $declaredReturnType, but was $returnType (in method $methodId)")

                case UpdateMethodDecl(_, operationLevel, _, body) =>
                    val returnType = typeOfExpr(body, varEnv)(MethodContext((classDecl.toType, thisConsistency), MutableContext, operationLevel), Local, classTable).effectiveType()
                    if (returnType.classType != Natives.unitType)
                        throw TypeError(s"return type is wrong. Expected: $Natives.UnitType, but was $returnType (in method $methodId)")
            }
        })
    }


    private def typeOfExpr(expr: IRExpr, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                       implicitContext: ConsistencyType,
                                                       classTable: ClassTable): Type = expr match {
        case True => CompoundType(Natives.booleanType, Local, Bottom)
        case False => CompoundType(Natives.booleanType, Local, Bottom)
        case UnitLiteral => CompoundType(Natives.unitType, Local, Bottom)
        case Num(_) => CompoundType(Natives.numberType, Local, Bottom)

        case Var(id: VarId) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case Let(id: VarId, namedExpr: IRExpr, body: IRExpr) =>
            val namedType = typeOfExpr(namedExpr, vars)
            typeOfExpr(body, vars + (id -> namedType))

        case If(conditionExpr, thenExpr, elseExpr) =>
            val condType = typeOfExpr(conditionExpr, vars).effectiveType()

            if (condType.classType != Natives.booleanType)
                throw TypeError(s"condition must be Bool, but was: $condType")

            val newImplicitContext = implicitContext glb condType.consistencyType

            val t1 = typeOfExpr(thenExpr, vars)(declarationContext, newImplicitContext, classTable)
            val t2 = typeOfExpr(elseExpr, vars)(declarationContext, newImplicitContext, classTable)

            if (t1 != t2) // TODO: use lub for expression type inference instead?
                throw TypeError(s"branches have diverging types: $t1 and $t2")

            t1

        case Equals(expr1, expr2) =>
            val t1 = typeOfExpr(expr1, vars).effectiveType()
            val t2 = typeOfExpr(expr2, vars).effectiveType()

            if (t1.classType != t2.classType)
                throw TypeError(s"non-matching types in <Equals>: $t1 and $t2")

            CompoundType(Natives.booleanType, t1.consistencyType lub t2.consistencyType, Mutable) // TODO: mutability type

        case Add(expr1, expr2) =>
            val t1 = typeOfExpr(expr1, vars).effectiveType()
            val t2 = typeOfExpr(expr2, vars).effectiveType()

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

                    val fieldType = fieldDecl.typ.effectiveType()

                    CompoundType(fieldType.classType, fieldType.consistencyType lub operationLevel.consistencyType(), fieldType.mutabilityType)
            }

        case SetField(fieldId: FieldId, value: IRExpr) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (mutabilityContext != MutableContext)
                        throw TypeError("assignment in immutable context: " + thisType)

                    val valueType = typeOfExpr(value, vars)

                    val cls = classTable.getOrElse((thisType._1.classId, thisType._2), throw TypeError(s"class of 'this' not available: $thisType"))
                    val fieldDecl = cls.getField(fieldId).getOrElse(throw TypeError(s"field not available: $fieldId (in class $thisType)"))
                    if (valueType !<= fieldDecl.typ)
                        throw TypeError(s"assignment has wrong type. expected: ${fieldDecl.typ} (but was: $valueType)")

                    if (fieldDecl.typ.effectiveType().mutabilityType == Immutable)
                        throw TypeError(s"wrong assignment of immutable field")

                    if (implicitContext !<= fieldDecl.typ.effectiveType().consistencyType)
                        throw TypeError(s"wrong assignment in implicit context: ${fieldDecl.typ} in $implicitContext context")

                    if (operationLevel.consistencyType() !<= fieldDecl.typ.effectiveType().consistencyType)
                        throw TypeError(s"wrong assignment in operation context: ${fieldDecl.typ} in ${operationLevel.consistencyType()} context")

                    valueType
            }

        case CallQuery(recv, methodId, arguments) =>
            val recvType = typeOfExpr(recv, vars).effectiveType()
            val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))
            val (mthdDecl, typeEnv) = checkMethodCall(recvType, methodId, vars, argTypes)

            val queryDecl = mthdDecl match {
                case q: QueryMethodDecl => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            resolveType(queryDecl.returnType, typeEnv)

        case CallUpdate(recv, methodId, arguments) =>
            val recvType = typeOfExpr(recv, vars).effectiveType()

            if (recvType.mutabilityType == Immutable)
                throw TypeError(s"invalid update call on immutable receiver: $methodId (in class ${recvType.classType.classId})")

            val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))
            val (mthdDecl, _) = checkMethodCall(recvType, methodId, vars, argTypes)

            if (!(implicitContext <= mthdDecl.operationLevel.consistencyType()))
                throw TypeError(s"wrong operation level in context: ${mthdDecl.operationLevel.consistencyType()} in $implicitContext")

            mthdDecl match {
                case _: UpdateMethodDecl =>
                case _ => throw TypeError(s"expected update method: $methodId")
            }

            CompoundType(Natives.unitType, Local, Bottom)

        case Sequence(exprs) =>
            exprs.foldLeft(null: Type)((r, e) => typeOfExpr(e, vars))

        case Transaction(body) =>
            typeOfExpr(body, vars)

        case New(_, classId, typeArgs, consistencyType, args) =>
            val classDecl = classTable.getOrElse((classId, consistencyType), throw TypeError(s"class not available: $consistencyType $classId"))

            if (typeArgs.length != classDecl.typeParameters.length)
                throw TypeError(s"wrong number of type arguments: $classId")

            (typeArgs zip classDecl.typeParameters).foreach(e => {
                val (arg, param) = e
                if (!(arg.effectiveType() <= param.effectiveType()))
                    throw TypeError(s"wrong type argument for type variable: $arg (expected: $param)")
            })

            if (args.size != classDecl.fields.size)
                throw TypeError(s"wrong number of constructor arguments: $classId")

            args.foreachEntry((fieldId, expr) => {
                val argType = typeOfExpr(expr, vars)
                val fieldType = classDecl.fields.getOrElse(fieldId,
                    throw TypeError(s"field not found in constructor: $fieldId (in class $classId)")).typ

                if (argType !<= fieldType)
                    throw TypeError(s"wrong constructor argument type: expected $fieldType, but was $argType (in class $classId)")
            })

            CompoundType(ClassType(classId, typeArgs), consistencyType, Mutable) // TODO: which mutability type here?

        case _ => ???
    }

    private def checkMethodCall(recvType: CompoundType, methodId: MethodId, vars: VarEnv, argTypes: Seq[Type])
                               (implicit declarationContext: DeclarationContext,
                                implicitContext: ConsistencyType,
                                classTable: ClassTable): (MethodDecl, TypeVarEnv) = {
        val recvClassDecl = classTable.getOrElse((recvType.classType.classId, recvType.consistencyType), throw TypeError(s"class not available: $recvType"))

        if (recvClassDecl.typeParameters.length != recvType.classType.typeArguments.length)
            throw TypeError(s"wrong number of type arguments: $recvType")

        val typeEnv: TypeVarEnv =
            (recvClassDecl.typeParameters zip recvType.classType.typeArguments).map(p => (p._1.typeVarId, p._2)).toMap

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

    private def resolveType(typ: Type, typeVars: TypeVarEnv): Type = typ match {
        case TypeVar(x, upperBound) => typeVars.getOrElse(x, resolveType(upperBound, typeVars))
        case CompoundType(ClassType(classId, typeArgs), c, m) =>
            CompoundType(ClassType(classId, typeArgs.map(typeArg => resolveType(typeArg, typeVars))), c, m)
    }
}
