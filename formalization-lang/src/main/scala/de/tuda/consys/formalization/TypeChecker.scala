package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.ClassTable.{ClassTable, mType}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.TypeError
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.types._

object TypeChecker {
    private sealed trait DeclarationContext

    private case object TopLevelContext extends DeclarationContext

    private case class MethodContext(thisType: ClassType,
                                     mutabilityContext: MutabilityType,
                                     operationLevel: ConsistencyType) extends DeclarationContext

    private type VarEnv = Map[VarId, Type]

    def checkProgram(programDecl: ProgramDecl): Unit = {
        programDecl.classTable.values.foreach(decl => checkClass(decl)(programDecl.classTable))

        for (p <- programDecl.processes)
            checkStatement(p, Map.empty)(
                TopLevelContext, Local,
                programDecl.classTable, Map.empty, Map.empty, Map.empty,
                transactionContext = false, None)
    }

    private def checkClass(classDecl: ClassDecl)(implicit classTable: ClassTable): Unit = {
        implicit val typeVarEnv: TypeVarEnv = classDecl.typeParametersToEnv
        implicit val tvmEnv: TypeVarMutabilityEnv = classDecl.typeParameterMutabilityBoundsToEnv
        implicit val consistencyVarEnv: ConsistencyVarEnv = classDecl.consistencyParametersToEnv

        if (classDecl.superClass.classId != topClassId && !classTable.contains(classDecl.superClass.classId))
            throw TypeError(s"unknown superclass ${classDecl.superClass.classId} (in ${classDecl.classId})")

        classDecl.fields.foreachEntry((id, decl) => {
            if (!wellFormed(decl.typ))
                throw TypeError(s"misformed type for field $id (in: ${classDecl.classId}")
            if (checkExpression(decl.init)(Map.empty, classTable, typeVarEnv, tvmEnv, consistencyVarEnv) !<= decl.typ)
                throw TypeError(s"invalid initializer for field $id (in: ${classDecl.classId}")
        })

        if (!wellFormed(classDecl.superClass.toClassType))
            throw TypeError(s"misformed superclass type (in: ${classDecl.classId}")

        classDecl.methods.foreachEntry((_, methodDecl) => {
            methodDecl match {
                case q: QueryMethodDecl =>
                    checkQuery(q)(classTable, classDecl.toType, typeVarEnv, tvmEnv, consistencyVarEnv)
                case u: UpdateMethodDecl =>
                    checkUpdate(u)(classTable, classDecl.toType, typeVarEnv, tvmEnv, consistencyVarEnv)
            }
        })
    }

    private def checkUpdate(method: UpdateMethodDecl)(implicit classTable: ClassTable,
                                                      thisType: ClassType,
                                                      typeVars: TypeVarEnv,
                                                      typMutVars: TypeVarMutabilityEnv,
                                                      consistencyVars: ConsistencyVarEnv): Unit = {
        val methodType = UpdateType(method.operationLevel, method.declaredParameters.map(x => x.typ), method.returnType)
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override (in ${thisType.classId}.${method.name})")

        if (!wellFormed(methodType.returnType))
            throw TypeError(s"misformed return type (in ${thisType.classId}.${method.name})")
        if (!wellFormed(methodType.operationLevel))
            throw TypeError(s"misformed operation level (in ${thisType.classId}.${method.name})")
        if (methodType.operationLevel.isInstanceOf[ConsistencyUnion])
            throw TypeError(s"misformed union operation level (in ${thisType.classId}.${method.name})")
        methodType.parameters.foreach(p =>
            if (!wellFormed(p))
                throw TypeError(s"misformed parameter type (in ${thisType.classId}.${method.name})")
        )

        method.body match {
            case Sequence(_, ReturnExpr(_)) =>
                val varEnv0 = method.declaredParametersToEnvironment
                checkStatement(method.body, varEnv0)(
                    MethodContext(thisType, Mutable, method.operationLevel), Local,
                    classTable, typeVars, typMutVars, consistencyVars,
                    transactionContext = true, Some(methodType.returnType))
            case Sequence(_, Error) =>
                val varEnv0 = method.declaredParametersToEnvironment
                checkStatement(method.body, varEnv0)(
                    MethodContext(thisType, Mutable, method.operationLevel), Local,
                    classTable, typeVars, typMutVars, consistencyVars,
                    transactionContext = true, Some(methodType.returnType))
            case Error =>
            case _ =>
                throw TypeError(s"invalid method body, no final return found (in ${thisType.classId}.${method.name})")
        }
    }

    private def checkQuery(method: QueryMethodDecl)(implicit classTable: ClassTable,
                                                    thisType: ClassType ,
                                                    typeVars: TypeVarEnv,
                                                    typMutVars: TypeVarMutabilityEnv,
                                                    consistencyVars: ConsistencyVarEnv): Unit = {
        val methodType = QueryType(method.operationLevel, method.declaredParameters.map(x => x.typ), method.returnType)
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override (in ${thisType.classId}.${method.name})")

        if (!wellFormed(methodType.returnType))
            throw TypeError(s"misformed return type (in ${thisType.classId}.${method.name})")
        if (!wellFormed(methodType.operationLevel))
            throw TypeError(s"misformed operation level (in ${thisType.classId}.${method.name})")
        if (methodType.operationLevel.isInstanceOf[ConsistencyUnion])
            throw TypeError(s"misformed union operation level (in ${thisType.classId}.${method.name})")
        methodType.parameters.foreach(p =>
            if (!wellFormed(p))
                throw TypeError(s"misformed parameter type (in ${thisType.classId}.${method.name})")
        )

        if (methodType.returnType.m != Immutable)
            throw TypeError(s"query must not have mutable return type (in ${thisType.classId}.${method.name})")

        method.body match {
            case Sequence(_, ReturnExpr(_)) =>
                val varEnv0 = method.declaredParametersToEnvironment
                checkStatement(method.body, varEnv0)(
                    MethodContext(thisType, Immutable, method.operationLevel), Local,
                    classTable, typeVars, typMutVars, consistencyVars,
                    transactionContext = true, Some(methodType.returnType))
            case Sequence(_, Error) =>
                val varEnv0 = method.declaredParametersToEnvironment
                checkStatement(method.body, varEnv0)(
                    MethodContext(thisType, Immutable, method.operationLevel), Local,
                    classTable, typeVars, typMutVars, consistencyVars,
                    transactionContext = true, Some(methodType.returnType))
            case Error =>
            case _ =>
                throw TypeError(s"invalid method body, no final return or error found (in ${thisType.classId}.${method.name})")
        }
    }

    private def checkOverride(id: MethodId, receiver: ClassType, overriding: MethodType)(implicit ct: ClassTable): Boolean = {
        val overridden = mType(id, receiver)
        (overriding, overridden) match {
            case (UpdateType(operationLevel1, parameters1, returnType1), UpdateType(operationLevel2, parameters2, returnType2)) =>
                operationLevel1 == operationLevel2 &&
                  returnType1 == returnType2 &&
                  parameters1.size == parameters2.size &&
                  (parameters1 zip parameters2).forall(p => p._1 == p._2)
            case (QueryType(operationLevel1, parameters1, returnType1), QueryType(operationLevel2, parameters2, returnType2)) =>
                operationLevel1 == operationLevel2 &&
                  returnType1 == returnType2 &&
                  parameters1.size == parameters2.size &&
                  (parameters1 zip parameters2).forall(p => p._1 == p._2)
            case _ => false
        }
    }

    private def checkExpression(expr: Expression)(implicit vars: VarEnv,
                                                  classTable: ClassTable,
                                                  typeVars: TypeVarEnv,
                                                  typMutVars: TypeVarMutabilityEnv,
                                                  consistencyVarEnv: ConsistencyVarEnv): Type = expr match {
        case Num(_) => Type(Local, Immutable, NumberTypeSuffix)

        case True => Type(Local, Immutable, BooleanTypeSuffix)

        case False => Type(Local, Immutable, BooleanTypeSuffix)

        case UnitLiteral => Type(Local, Immutable, UnitTypeSuffix)

        case StringLiteral(_) => Type(Local, Immutable, StringTypeSuffix)

        case Ref(_, classType) =>
            val typ = Type(Local, Mutable, RefTypeSuffix(classType))
            if (!wellFormed(typ))
                throw TypeError("misformed type in ref")
            typ

        case LocalObj(classType, constructor) =>
            val fieldTypes = ClassTable.fields(classType).map(f => f._1 -> f._2.typ)
            val constructorTypes = constructor.map(e => e._1 -> checkExpression(e._2))
            if (constructorTypes.size != fieldTypes.size)
                throw TypeError("wrong constructor size")

            fieldTypes.foreachEntry((id, fieldType) => {
                constructorTypes.get(id) match {
                    case Some(consType) if consType !<= fieldType =>
                        throw TypeError(s"wrong constructor for field $id: was $consType, expected $fieldType")
                    case None =>
                        throw TypeError(s"missing constructor for field $id")
                    case _ => ()
                }
            })

            val typ = Type(Local, Immutable, LocalTypeSuffix(classType))
            if (!wellFormed(typ)) {
                throw TypeError(s"misformed local type: $typ")
            }
            typ

        case Default(s, m) =>
            val typ = Type(Local, m, s)
            if (!wellFormed(typ))
                throw TypeError(s"misformed default type: $typ")
            typ

        case Var(id) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case Equals(e1, e2) =>
            val Type(l1, _, t1) = checkExpression(e1)
            val Type(l2, _, t2) = checkExpression(e2)

            if (t1 != t2)
                throw TypeError(s"non-matching types in <Equals>: $t1 and $t2")

            Type(ConsistencyUnion(l1, l2), Immutable, BooleanTypeSuffix)

        case ArithmeticOperation(e1, e2, _) =>
            (checkExpression(e1), checkExpression(e2)) match {
                case (Type(l1, Immutable, NumberTypeSuffix), Type(l2, Immutable, NumberTypeSuffix)) =>
                    Type(ConsistencyUnion(l1, l2), Immutable, NumberTypeSuffix)
                case (t1, t2) =>
                    throw TypeError(s"invalid types for <ArithmeticOperation>: $t1 and $t2")
            }

        case ArithmeticComparison(e1, e2, _) =>
            (checkExpression(e1), checkExpression(e2)) match {
                case (Type(l1, Immutable, NumberTypeSuffix), Type(l2, Immutable, NumberTypeSuffix)) =>
                    Type(ConsistencyUnion(l1, l2), Immutable, BooleanTypeSuffix)
                case (t1, t2) =>
                    throw TypeError(s"invalid types for <ArithmeticComparison>: $t1 and $t2")
            }

        case BooleanCombination(e1, e2, _) =>
            (checkExpression(e1), checkExpression(e2)) match {
                case (Type(l1, Immutable, BooleanTypeSuffix), Type(l2, Immutable, BooleanTypeSuffix)) =>
                    Type(ConsistencyUnion(l1, l2), Immutable, BooleanTypeSuffix)
                case (t1, t2) =>
                    throw TypeError(s"invalid types for <BooleanCombination>: $t1 and $t2")
            }
    }

    private def checkExpressionWithVars(expr: Expression, vars: VarEnv)(implicit classTable: ClassTable,
                                                                        typeVars: TypeVarEnv,
                                                                        typMutVars: TypeVarMutabilityEnv,
                                                                        consistencyVarEnv: ConsistencyVarEnv): Type =
        checkExpression(expr)(vars, implicitly, implicitly, implicitly, implicitly)

    private def checkStatement(statement: Statement, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                                   implicitContext: ConsistencyType,
                                                                   classTable: ClassTable,
                                                                   typeVars: TypeVarEnv,
                                                                   typMutVars: TypeVarMutabilityEnv,
                                                                   consistencyVars: ConsistencyVarEnv,
                                                                   transactionContext: Boolean,
                                                                   retType: Option[Type]): Unit = statement match {
        case Skip =>

        case Error =>

        case ReturnExpr(e) =>
            retType match {
                case Some(retTypeValue) =>
                    val typ = checkExpressionWithVars(e, vars)
                    if (typ !<= retTypeValue) {
                        throw TypeError(s"invalid return expression type: was $typ, expected: $retTypeValue")
                    }
                case None => throw TypeError(s"invalid return statement: expected none")
            }

        case Block(varDecls, s) =>
            if (varDecls.exists(v => vars.contains(v._2)))
                throw TypeError("invalid variable shadowing in block")
            varDecls.foreach(e => {
                if (!wellFormed(e._1))
                    throw TypeError(s"misformed type for block variable ${e._2}")
                if (checkExpressionWithVars(e._3, vars) !<= e._1)
                    throw TypeError(s"invalid initializer for block variable ${e._2}")
            })
            checkStatement(s, vars ++ varDecls.map(d => d._2 -> d._1))

        case Sequence(s1, s2) =>
            checkStatement(s1, vars)
            checkStatement(s2, vars)

        case If(conditionExpr, thenStmt, elseStmt) =>
            val conditionType = checkExpressionWithVars(conditionExpr, vars)
            conditionType match {
                case Type(l, Immutable, BooleanTypeSuffix) =>
                    val newImplicitContext = ConsistencyUnion(implicitContext, l)
                    checkStatement(thenStmt, vars)(
                        implicitly, newImplicitContext,
                        implicitly, implicitly, implicitly, implicitly,
                        implicitly, implicitly)
                    checkStatement(elseStmt, vars)(
                        implicitly, newImplicitContext,
                        implicitly, implicitly, implicitly, implicitly,
                        implicitly, implicitly)
                case _ =>
                    throw TypeError(s"incorrect type for condition in if: $conditionType")
            }

        case While(condition, stmt) =>
            val conditionType = checkExpressionWithVars(condition, vars)
            conditionType match {
                case Type(l, Immutable, BooleanTypeSuffix) =>
                    val newImplicitContext = ConsistencyUnion(implicitContext, l)
                    checkStatement(stmt, vars)(
                        implicitly, newImplicitContext,
                        implicitly, implicitly, implicitly, implicitly,
                        implicitly, implicitly)
                case _ =>
                    throw TypeError(s"incorrect type for condition in while: $conditionType")
            }

        case Let(varId, e) =>
            val varType = vars.getOrElse(varId, throw TypeError(s"assignment to undeclared variable $varId"))
            val eType = checkExpressionWithVars(e, vars)
            if (eType !<= varType)
                throw TypeError(s"incompatible type for assignment: $varId ($eType)")

        case SetField(fieldId, valueExpr) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (mutabilityContext != Mutable)
                        throw TypeError("assignment in immutable context: " + thisType)

                    val valueType = checkExpressionWithVars(valueExpr, vars)

                    val fieldType = ClassTable.fields(thisType).get(fieldId) match {
                        case Some(value) => value.typ
                        case None => throw TypeError(s"field not found: $fieldId (in class $thisType)")
                    }

                    if (valueType !<= fieldType)
                        throw TypeError(s"assignment has wrong type. expected: $fieldType (but was: $valueType)")

                    if (implicitContext !<= fieldType.l)
                        throw TypeError(s"wrong assignment in implicit context: $fieldType in $implicitContext context")

                    if (operationLevel !<= fieldType.l)
                        throw TypeError(s"wrong assignment in operation context: " +
                            s"$fieldType in $operationLevel context")
            }

        case GetField(varId, fieldId) => declarationContext match {
            case TopLevelContext =>
                throw TypeError("cannot resolve 'this' outside of class declaration")

            case MethodContext(thisType, mutabilityContext, operationLevel) =>
                if (!vars.contains(varId))
                    throw TypeError(s"assignment to undeclared variable $varId")

                val fieldType = ClassTable.fields(thisType).get(fieldId) match {
                    case Some(value) => value.typ
                    case None => throw TypeError(s"field not found: $fieldId (in class $thisType)")
                }

                val typ = Type(ConsistencyUnion(fieldType.l, operationLevel),
                    fieldType.m lub mutabilityContext,
                    fieldType.suffix)

                if (typ !<= vars(varId))
                    throw TypeError(s"invalid assignment (was $typ, expected ${vars(varId)}) in $declarationContext")
        }

        case CallUpdate(recvExpr, methodId, arguments) =>
            val recvType = bound(checkExpressionWithVars(recvExpr, vars))
            if (!recvType.suffix.isInstanceOf[RefTypeSuffix])
                throw TypeError("invalid update call on non-ref receiver")
            if (recvType.m == Immutable)
                throw TypeError(s"invalid update call on immutable receiver: " +
                    s"$methodId (on receiver $recvType)")

            val methodType = mType(methodId, recvType.suffix.asInstanceOf[RefTypeSuffix].classType) match {
                case u: UpdateType => u
                case _ => throw TypeError(s"expected update method, but got: $methodId")
            }

            if (arguments.size != methodType.parameters.size)
                throw TypeError(s"wrong number of arguments for method $methodId: ${arguments.size}")

            val argTypes = arguments.map(argExpr => checkExpressionWithVars(argExpr, vars))
            (argTypes zip methodType.parameters).foreach(p => {
                val (argType, paramType) = p
                if (argType !<= paramType)
                    throw TypeError(s"wrong argument type: was $argType but expected $paramType")
            })

            if (recvType.l !<= methodType.operationLevel)
                throw TypeError(s"wrong operation level for receiver: " +
                    s"${methodType.operationLevel} for $recvType")

            if (implicitContext !<= methodType.operationLevel)
                throw TypeError(s"wrong operation level in context: " +
                    s"${methodType.operationLevel} in $implicitContext")

            declarationContext match {
                case TopLevelContext =>
                case MethodContext(_, mutabilityContext, operationLevel) =>
                    if (operationLevel !<= methodType.operationLevel)
                        throw TypeError(s"wrong operation level in method context: " +
                            s"${methodType.operationLevel} in $operationLevel")

                    if (mutabilityContext == Immutable)
                        throw TypeError(s"update call in query: $methodId")
            }

        case CallUpdateThis(methodId, arguments) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("'this' not found")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    val methodType = mType(methodId, thisType) match {
                        case q: QueryType => q
                        case _ => throw TypeError(s"expected query method: $methodId")
                    }

                    if (arguments.size != methodType.parameters.size)
                        throw TypeError(s"wrong number of arguments for method $methodId: ${arguments.size}")

                    val argTypes = arguments.map(argExpr => checkExpressionWithVars(argExpr, vars))
                    (argTypes zip methodType.parameters).foreach(p => {
                        val (argType, paramType) = p
                        if (argType !<= paramType)
                            throw TypeError(s"wrong argument type: was $argType but expected $paramType")
                    })

                    if (implicitContext !<= methodType.operationLevel)
                        throw TypeError("wrong operation level for implicit context")

                    if (operationLevel !<= methodType.operationLevel)
                        throw TypeError("wrong operation level for method context")

                    if (mutabilityContext == Immutable)
                        throw TypeError(s"update call in query: $methodId")
            }

        case CallQuery(varId, recvExpr, methodId, argumentExprs) =>
            if (!vars.contains(varId))
                throw TypeError(s"assignment to undeclared variable $varId")

            val recvType = bound(checkExpressionWithVars(recvExpr, vars))
            val recvClassType = recvType.suffix match {
                case RefTypeSuffix(classType) => classType
                case LocalTypeSuffix(classType) => classType
            }

            val methodType = mType(methodId, recvClassType) match {
                case q: QueryType => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            if (argumentExprs.size != methodType.parameters.size)
                throw TypeError(s"wrong number of arguments for method $methodId: ${argumentExprs.size}")

            val argTypes = argumentExprs.map(argExpr => checkExpressionWithVars(argExpr, vars))
            (argTypes zip methodType.parameters).foreach(p => {
                val (argType, paramType) = p
                if (argType !<= paramType)
                    throw TypeError(s"wrong argument type: was $argType but expected $paramType")
            })

            val resType = Type(ConsistencyUnion(methodType.returnType.l, recvType.l),
                methodType.returnType.m,
                methodType.returnType.suffix)

            if (resType !<= vars(varId))
                throw TypeError(s"invalid assignment: was $resType, expected ${vars(varId)}")

        case CallQueryThis(varId, methodId, argumentExprs) =>
            if (!vars.contains(varId))
                throw TypeError(s"assignment to undeclared variable $varId")

            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("'this' not found")

                case MethodContext(thisType, _, operationLevel) =>
                    val methodType = mType(methodId, thisType) match {
                        case q: QueryType => q
                        case _ => throw TypeError(s"expected query method: $methodId")
                    }

                    if (argumentExprs.size != methodType.parameters.size)
                        throw TypeError(s"wrong number of arguments for method $methodId: ${argumentExprs.size}")

                    val argTypes = argumentExprs.map(argExpr => checkExpressionWithVars(argExpr, vars))
                    (argTypes zip methodType.parameters).foreach(p => {
                        val (argType, paramType) = p
                        if (argType !<= paramType)
                            throw TypeError(s"wrong argument type: was $argType but expected $paramType")
                    })

                    val resType = Type(ConsistencyUnion(methodType.returnType.l, operationLevel),
                        methodType.returnType.m,
                        methodType.returnType.suffix)

                    if (resType !<= vars(varId))
                        throw TypeError("invalid assignment (incorrect type)")
            }

        case Replicate(varId, _, classType, constructor) =>
            if (!vars.contains(varId))
                throw TypeError(s"assignment to undeclared variable $varId")

            val fieldTypes = ClassTable.fields(classType).map(f => f._1 -> f._2.typ)
            val constructorTypes = constructor.map(e => e._1 -> checkExpressionWithVars(e._2, vars))
            if (constructorTypes.size != fieldTypes.size)
                throw TypeError("wrong constructor size")

            fieldTypes.foreachEntry((id, fieldType) => {
                constructorTypes.get(id) match {
                    case Some(consType) if consType !<= fieldType =>
                        throw TypeError(s"wrong constructor for field $id: was $consType but expected $fieldType")
                    case None =>
                        throw TypeError(s"missing constructor for field $id")
                    case _ => ()
                }
            })

            val typ = Type(Local, Mutable, RefTypeSuffix(classType))
            if (!wellFormed(typ))
                throw TypeError("misformed type in replicate")
            if (typ !<= vars(varId))
                throw TypeError("invalid assignment (incorrect type)")

        case Transaction(body, except) =>
            if (transactionContext)
                throw TypeError("invalid nested transaction")
            if (retType.isDefined)
                throw TypeError("invalid transaction in method")

            checkStatement(body, vars)(
                implicitly, implicitly,
                implicitly, implicitly, implicitly, implicitly,
                transactionContext = true, implicitly)
            checkStatement(except, vars)(
                implicitly, implicitly,
                implicitly, implicitly, implicitly, implicitly,
                transactionContext = false, implicitly)

        case Print(expression) =>
            checkExpressionWithVars(expression, vars)
    }
}
