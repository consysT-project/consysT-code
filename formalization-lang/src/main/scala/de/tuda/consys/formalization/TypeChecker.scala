package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.types._
import de.tuda.consys.formalization.lang.errors.TypeError

// TODO: check transactions
// TODO: check invalid identifier 'this' (since we don't have a parser yet)
object TypeChecker {
    private sealed trait MethodMutabilityContext

    private case object ImmutableContext extends MethodMutabilityContext

    private case object MutableContext extends MethodMutabilityContext

    private sealed trait DeclarationContext

    private case object TopLevelContext extends DeclarationContext

    private case class MethodContext(thisType: ClassType,
                                     mutabilityContext: MethodMutabilityContext,
                                     operationLevel: OperationLevel) extends DeclarationContext

    private type VarEnv = Map[VarId, Type]

    def checkProgram(programDecl: ProgramDecl): Unit = {
        programDecl.classTable.values.foreach(decl => checkClass(decl)(programDecl.classTable))

        val r = checkStatement(programDecl.body, Map.empty)(TopLevelContext, Local, programDecl.classTable, Map.empty)
        typeOfExpr(programDecl.returnExpr, r)(TopLevelContext, Local, programDecl.classTable, Map.empty)
    }

    private def checkClass(classDecl: ClassDecl)(implicit classTable: ClassTable): Unit = {
        classDecl.methods.foreachEntry((methodId, methodDecl) => {
            val varEnv: VarEnv = methodDecl.declaredParameters.map(varDecl => varDecl.name -> varDecl.typ).toMap
            implicit val typeVarEnv: TypeVarEnv = classDecl.typeParametersToEnv

            methodDecl match {
                case QueryMethodDecl(_, operationLevel, declaredParameters, declaredReturnType, body) =>
                    val returnType = resolveType(
                        typeOfExpr(body, varEnv)(MethodContext(classDecl.toType, ImmutableContext, operationLevel), Local, classTable, typeVarEnv),
                        typeVarEnv)
                    val resolvedDeclaredReturnType = resolveType(declaredReturnType, typeVarEnv)
                    val resolvedDeclaredArgumentTypes = declaredParameters.map(p => p.typ).map(t => resolveType(t, typeVarEnv))

                    classDecl.getMethodOverride(methodId) match {
                        case Some(value: QueryMethodDecl) =>
                            if (resolvedDeclaredReturnType !<= resolveType(value.returnType, typeVarEnv))
                                throw TypeError(s"wrong return type in method override (in method  ${classDecl.classId}.$methodId")
                            for (a <- resolvedDeclaredArgumentTypes;
                                 b <- value.declaredParameters.map(p => p.typ).map(t => resolveType(t, typeVarEnv))) {
                                if (a !>= b)
                                    throw TypeError(s"wrong argument type in method override (in method  ${classDecl.classId}.$methodId")
                            }
                        case Some(_: UpdateMethodDecl) => throw TypeError(s"cannot override update method with query method: ${classDecl.classId}.$methodId")
                        case None => // nothing to do
                    }

                    if (returnType !<= resolvedDeclaredReturnType)
                        throw TypeError(s"return type is wrong. Expected: $resolvedDeclaredReturnType, but was $returnType (in method ${classDecl.classId}.$methodId})")

                case UpdateMethodDecl(_, operationLevel, declaredParameters, body) =>
                    val returnType = resolveType(
                        typeOfExpr(body, varEnv)(MethodContext(classDecl.toType, MutableContext, operationLevel), Local, classTable, typeVarEnv),
                        typeVarEnv)

                    classDecl.getMethodOverride(methodId) match {
                        case Some(value: UpdateMethodDecl) =>
                            val resolvedDeclaredArgumentTypes = declaredParameters.map(p => p.typ).map(t => resolveType(t, typeVarEnv))
                            for (a <- resolvedDeclaredArgumentTypes;
                                 b <- value.declaredParameters.map(p => p.typ).map(t => resolveType(t, typeVarEnv))) {
                                if (a !>= b)
                                    throw TypeError(s"wrong argument type in method override (in method  ${classDecl.classId}.$methodId")
                            }
                        case Some(_: QueryMethodDecl) => throw TypeError(s"cannot override query method with update method: ${classDecl.classId}.$methodId")
                        case None => // nothing to do
                    }

                    if (returnType.classType != Natives.unitType)
                        throw TypeError(s"return type is wrong. Expected: $Natives.UnitType, but was $returnType (in method $methodId)")
            }
        })
    }

    private def typeOfExpr(expr: Expression, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                           implicitContext: ConsistencyType,
                                                           classTable: ClassTable,
                                                           typeVars: TypeVarEnv): Type = expr match {
        case True => CompoundClassType(Natives.booleanType, Local, Immutable)
        case False => CompoundClassType(Natives.booleanType, Local, Immutable)
        case UnitLiteral => CompoundClassType(Natives.unitType, Local, Immutable)
        case Num(_) => CompoundClassType(Natives.numberType, Local, Immutable)

        case Var(id: VarId) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case Equals(expr1, expr2) =>
            val t1 = bound(typeOfExpr(expr1, vars))
            val t2 = bound(typeOfExpr(expr2, vars))

            if (t1 != t2) // TODO
                throw TypeError(s"non-matching types in <Equals>: $t1 and $t2")

            CompoundClassType(Natives.booleanType, t1.consistencyType lub t2.consistencyType, Immutable)

        case Add(expr1, expr2) =>
            val t1 = typeOfExpr(expr1, vars)
            val t2 = typeOfExpr(expr2, vars)

            (t1, t2) match {
                case (CompoundClassType(Natives.numberType, c1, _), CompoundClassType(Natives.numberType, c2, _)) =>
                    CompoundClassType(Natives.numberType, c1 lub c2, Immutable)
                case _ =>
                    throw TypeError(s"invalid types for <Add>: $t1 and $t2")
            }

        case This =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside of class declaration")

                case MethodContext(classType, _, _) =>
                    ???
            }
    }

    private def checkMethodCall(recvType: CompoundClassType, methodId: MethodId, argTypes: Seq[Type])
                               (implicit declarationContext: DeclarationContext,
                                implicitContext: ConsistencyType,
                                classTable: ClassTable): (MethodDecl, TypeVarEnv) = {
        val recvClassDecl = classTable.getOrElse((recvType.classType.classId, recvType.consistencyType), throw TypeError(s"class not available: $recvType"))

        if (recvClassDecl.typeParameters.length != recvType.classType.typeArguments.length)
            throw TypeError(s"wrong number of type arguments: $recvType")

        val methodDecl: MethodDecl = recvClassDecl.getMethod(methodId)
            .getOrElse(throw TypeError(s"method not available: $methodId (in class ${recvType.classType.classId})"))

        if (argTypes.size != methodDecl.declaredParameters.size)
            throw TypeError(s"wrong number of arguments for method $methodId: ${argTypes.size} (expected: ${methodDecl.declaredParameters.size}")

        implicit val typeEnv: TypeVarEnv =
            (recvClassDecl.typeParameters zip recvType.classType.typeArguments).map(p => (p._1.name, p._2)).toMap

        (argTypes zip methodDecl.declaredParameterTypes).foreach(t => {
            val argType = t._1
            val parameterType = resolveType(t._2, typeEnv)
            if (!(argType <= parameterType))
                throw TypeError(s"wrong argument type for method $methodId: $argType (expected: $parameterType)")
        })

        (methodDecl, typeEnv)
    }

    private def checkRhsAssign(assign: AssignRhs, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                  implicitContext: ConsistencyType,
                                                  classTable: ClassTable,
                                                  typeVars: TypeVarEnv): Type = assign match {
        case rhsExpression(e) =>
            typeOfExpr(e, vars)

        case rhsGetField(fieldId) => declarationContext match {
            case TopLevelContext =>
                throw TypeError("cannot resolve 'this' outside of class declaration")

            case MethodContext(thisType, _, operationLevel) =>
                val classDecl = classTable
                    .getOrElse(thisType.classId, throw TypeError(s"class of 'this' not available: $thisType"))

                val fieldDecl = classDecl.getField(fieldId).
                    getOrElse(throw TypeError(s"field not available: $fieldId (in class ${thisType.classId})"))

                val fieldType = bound(fieldDecl.typ)
                val readConsistency = fieldType.consistencyType lub operationLevel.consistencyType()
                fieldType.withConsistency(readConsistency)
        }

        case rhsCallQuery(recvExpr, methodId, argumentExprs) =>
            val recvType = bound(typeOfExpr(recvExpr, vars))
            val argTypes = argumentExprs.map(argExpr => typeOfExpr(argExpr, vars))

            val methodType = methodType(methodId, recvType)
            val (methodDecl, recvTypeEnv) = checkMethodCall(recvType, methodId, argTypes)

            val queryDecl = methodDecl match {
                case q: QueryMethodDecl => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            // TODO: adapt to receiver consistency
            val resultType = resolveType(queryDecl.returnType, recvTypeEnv)
        case rhsReplicate(location, classId, typeArguments, constructorExprs, consistency, mutability) => ???
        case rhsLookup(location) => ???
    }

    private def checkStatement(statement: Statement, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                                   implicitContext: ConsistencyType,
                                                                   classTable: ClassTable,
                                                                   typeVars: TypeVarEnv): VarEnv = statement match {
        case Sequence(s1, s2) =>
            val r1 = checkStatement(s1, vars)
            checkStatement(s2, r1)

        case If(conditionExpr, thenStmt, elseStmt) =>
            val conditionType = typeOfExpr(conditionExpr, vars)
            conditionType match {
                case CompoundClassType(Natives.booleanType, consistencyType, _) =>
                    implicit val implicitContext: ConsistencyType = implicitContext glb consistencyType
                    checkStatement(thenStmt, vars)
                    checkStatement(elseStmt, vars)
                    vars

                case _ =>
                    throw TypeError(s"incorrect type for condition: $conditionType")
            }

        case Let(varId, rhs) =>
            val namedType = checkRhsAssign(rhs, vars)
            vars + (varId -> namedType)

        case Assign(varId, rhs) =>
            val varType = vars.getOrElse(varId, throw TypeError(s"undeclared variable $varId"))
            val namedType = checkRhsAssign(rhs, vars)
            if (namedType !<= varType)
                throw TypeError(s"incompatible type for assignment: $varId ($namedType)")

        case SetField(fieldId, valueExpr) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (mutabilityContext != MutableContext)
                        throw TypeError("assignment in immutable context: " + thisType)

                    val valueType = typeOfExpr(valueExpr, vars)

                    val classDecl = classTable.getOrElse(thisType.classId,
                        throw TypeError(s"class of 'this' not available: $thisType"))
                    val fieldDecl = classDecl.getField(fieldId).getOrElse(
                        throw TypeError(s"field not available: $fieldId (in class $thisType)"))

                    val fieldType = fieldDecl.typ
                    val boundedFieldType = bound(fieldType)

                    if (valueType !<= fieldType)
                        throw TypeError(s"assignment has wrong type. expected: $boundedFieldType (but was: $valueType)")

                    if (boundedFieldType.mutabilityType == Immutable)
                        throw TypeError(s"wrong assignment of immutable field")

                    if (implicitContext !<= boundedFieldType.consistencyType)
                        throw TypeError(s"wrong assignment in implicit context: ${fieldDecl.typ} in $implicitContext context")

                    if (operationLevel.consistencyType() !<= boundedFieldType.consistencyType)
                        throw TypeError(s"wrong assignment in operation context: ${fieldDecl.typ} in ${operationLevel.consistencyType()} context")

                    vars
            }

            vars + (varId -> resultType)

        case CallUpdate(recvExpr, methodId, argumentExprs) =>
            val recvType = resolveType(typeOfExpr(recvExpr, vars), typeVars)

            if (recvType.mutabilityType == Immutable)
                throw TypeError(s"invalid update call on immutable receiver: $methodId (in class ${recvType.classType.classId})")

            val argTypes = argumentExprs.map(argExpr => typeOfExpr(argExpr, vars))
            val (methodDecl, _) = checkMethodCall(recvType, methodId, argTypes)

            if (!(implicitContext <= methodDecl.operationLevel.consistencyType()))
                throw TypeError(s"wrong operation level in context: ${methodDecl.operationLevel.consistencyType()} in $implicitContext")

            methodDecl match {
                case _: UpdateMethodDecl =>
                case _ => throw TypeError(s"expected update method: $methodId")
            }

            vars

        case Transaction(body, except) =>
            checkStatement(body, vars)
            checkStatement(except, vars)
            vars

        case Replicate(varId, location, classId, typeArguments, constructorExprs, consistency, mutability) =>
            val classDecl = classTable.getOrElse(classId, throw TypeError(s"class not available: $classId"))

            if (typeArguments.length != classDecl.typeParameters.length)
                throw TypeError(s"wrong number of type arguments: $classId")

            val classVarEnv = classDecl.typeParameters.map(p => p.name -> p.upperBound).toMap

            (typeArguments zip classDecl.typeParameters).foreach(e => {
                val (arg, paramDecl) = e
                val paramBound = resolveType(TypeVar(paramDecl.name), classVarEnv)
                if (arg !<= paramBound)
                    throw TypeError(s"wrong type argument for type variable: $arg (expected: $paramDecl)")
            })

            if (constructorExprs.size != classDecl.fields.size)
                throw TypeError(s"wrong number of constructor arguments: $classId")

            constructorExprs.foreachEntry((fieldId, expr) => {
                val argType = resolveType(typeOfExpr(expr, vars), typeVars)
                val field = classDecl.fields.getOrElse(fieldId,
                    throw TypeError(s"field not found in constructor: $fieldId (in class $classId)"))
                val fieldType = resolveType(field.typ, classVarEnv)

                if (argType !<= fieldType)
                    throw TypeError(s"wrong constructor argument type: expected $fieldType, but was $argType (in class $classId)")
            })

            // TODO: check location typing

            val resultType = CompoundType(types.ClassType(classId, typeArguments), consistency, mutability)
            vars + (varId -> resultType)

        case Lookup(varId, location) => ???
    }
}
