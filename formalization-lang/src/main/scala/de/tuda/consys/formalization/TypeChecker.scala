package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.ClassTable.{ClassTable, mType}
import de.tuda.consys.formalization.lang.Natives.natives
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.TypeError
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.types._

// TODO: check transactions
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
            checkStatement(p, Map.empty)(TopLevelContext, Local, programDecl.classTable, Map.empty, Map.empty, Map.empty)
    }

    private def checkClass(classDecl: ClassDecl)(implicit classTable: ClassTable): Unit = {
        implicit val typeVarEnv: TypeVarEnv = classDecl.typeParametersToEnv
        implicit val tvmEnv: TypeVarMutabilityEnv = classDecl.typeParameterMutabilityBoundsToEnv
        implicit val consistencyVarEnv: ConsistencyVarEnv = classDecl.consistencyParametersToEnv

        if (!classTable.contains(classDecl.superClass.classId))
            throw TypeError(s"unknown superclass ${classDecl.superClass.classId} (in ${classDecl.classId})")

        if (natives.contains(classDecl.superClass.classId))
            throw TypeError(s"cannot subclass native classes (in: ${classDecl.classId}")

        classDecl.fields.foreachEntry((id, decl) =>
            if (!wellFormed(decl.typ))
                throw TypeError(s"misformed type for field $id (in: ${classDecl.classId}")
        )

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
        val methodType = UpdateType(method.operationLevel, method.declaredParameters.map(x => x.typ))
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override: ${method.name}")

        // TODO: check well formedness of parameter types
        // TODO: check well formedness of op levels

        method.body match {
            case Sequence(_, Return) =>
                val varEnv0 = method.declaredParametersToEnvironment
                checkStatement(method.body, varEnv0)(
                    MethodContext(thisType, Mutable, method.operationLevel), Local, classTable, typeVars, typMutVars, consistencyVars)
            case _ =>
                throw TypeError("invalid method body") // TODO
        }
    }

    private def checkQuery(method: QueryMethodDecl)(implicit classTable: ClassTable,
                                                    thisType: ClassType ,
                                                    typeVars: TypeVarEnv,
                                                    typMutVars: TypeVarMutabilityEnv,
                                                    consistencyVars: ConsistencyVarEnv): Unit = {
        val methodType = QueryType(method.operationLevel, method.declaredParameters.map(x => x.typ), method.returnType)
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override: ${method.name}")

        // TODO: check well formedness of parameter types
        // TODO: check well formedness of return type
        // TODO: check well formedness of op levels

        val methodContext = MethodContext(thisType, Immutable, method.operationLevel)

        if (methodType.returnType.m != Immutable)
            throw TypeError(s"query must not have mutable return type: ${method.name} in ${thisType.classId}")

        method.body match {
            case Sequence(_, ReturnExpr(e)) =>
                val varEnv0 = method.declaredParametersToEnvironment
                val varEnv1 = checkStatement(method.body, varEnv0)(methodContext, Local, classTable, typeVars, typMutVars, consistencyVars)
            case _ =>
                throw TypeError("invalid method body") // TODO
        }
    }

    private def checkOverride(id: MethodId, receiver: ClassType, overriding: MethodType)(implicit ct: ClassTable): Boolean = {
        val overridden = mType(id, receiver)
        (overriding, overridden) match {
            case (UpdateType(operationLevel1, parameters1), UpdateType(operationLevel2, parameters2)) =>
                operationLevel1 == operationLevel2 &&
                    parameters1.size == parameters2.size &&
                    (parameters1 zip parameters2).forall(p => p._1 == p._2)
            case (QueryType(operationLevel1, parameters1, returnType1), QueryType(operationLevel2, parameters2, returnType2)) =>
                operationLevel1 == operationLevel2 &&
                    returnType1 == returnType2 &&
                    parameters1.size == parameters2.size &&
                    (parameters1 zip parameters2).forall(p => p._1 == p._2)
        }
    }

    // TODO: well-formedness checks
    private def checkExpression(expr: Expression)(implicit vars: VarEnv,
                                                  classTable: ClassTable,
                                                  typeVars: TypeVarEnv,
                                                  typMutVars: TypeVarMutabilityEnv,
                                                  consistencyVarEnv: ConsistencyVarEnv): Type = expr match {
        case Num(_) => Type(Local, Immutable, LocalTypeSuffix(Natives.numberType))

        case True => Type(Local, Immutable, LocalTypeSuffix(Natives.booleanType))

        case False => Type(Local, Immutable, LocalTypeSuffix(Natives.booleanType))

        case UnitLiteral => Type(Local, Immutable, LocalTypeSuffix(Natives.unitType))

        case Ref(id, classType, l, m) => Type(l, m, RefTypeSuffix(classType))

        case LocalObj(classType, constructor) =>
            val fieldTypes = ClassTable.fields(classType).map(f => f._1 -> f._2.typ)
            val constructorTypes = constructor.map(e => e._1 -> checkExpression(e._2))
            if (constructorTypes.size != fieldTypes.size)
                throw TypeError("wrong constructor size")

            fieldTypes.foreachEntry((id, fieldType) => {
                constructorTypes.get(id) match {
                    case Some(consType) if consType !<= fieldType =>
                        throw TypeError(s"wrong constructor for field $id")
                    case None =>
                        throw TypeError(s"missing constructor for field $id")
                    case _ => ()
                }
            })

            val typ = Type(Local, Immutable, LocalTypeSuffix(classType))
            if (!wellFormed(typ)) {
                throw TypeError(s"misformed type")
            }
            typ

        case Var(id) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case Equals(e1, e2) =>
            val Type(l1, _, t1) = checkExpression(e1)
            val Type(l2, _, t2) = checkExpression(e2)

            if (t1 != t2)
                throw TypeError(s"non-matching types in <Equals>: $t1 and $t2")

            Type(l1 lub l2, Immutable, LocalTypeSuffix(Natives.booleanType))

        case ArithmeticOperation(e1, e2) =>
            (checkExpression(e1), checkExpression(e2)) match {
                case (Type(l1, Immutable, LocalTypeSuffix(Natives.numberType)), Type(l2, Immutable, LocalTypeSuffix(Natives.numberType))) =>
                    Type(l1 lub l2, Immutable, LocalTypeSuffix(Natives.numberType))
                case (t1, t2) =>
                    throw TypeError(s"invalid types for <Add>: $t1 and $t2")
            }
    }

    private def checkExpressionWithVars(expr: Expression, vars: VarEnv)(implicit classTable: ClassTable,
                                                                        typeVars: TypeVarEnv,
                                                                        typMutVars: TypeVarMutabilityEnv,
                                                                        consistencyVarEnv: ConsistencyVarEnv): Type =
        checkExpression(expr)(vars, implicitly, implicitly, implicitly)

    private def checkStatement(statement: Statement, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                                   implicitContext: ConsistencyType,
                                                                   classTable: ClassTable,
                                                                   typeVars: TypeVarEnv,
                                                                   typMutVars: TypeVarMutabilityEnv,
                                                                   consistencyVars: ConsistencyVarEnv,
                                                                   transactionContext: Boolean,
                                                                   retType: Type): VarEnv = statement match {
        case Skip => vars

        case Error => vars

        case Return => vars

        case ReturnExpr(e) =>
            checkExpressionWithVars(e, vars)
            vars

        case Block(varDecls, s) =>
            if (varDecls.exists(v => vars.contains(v)))
                throw TypeError("variable shadowing in block") // TODO
            checkStatement(s, vars)
            vars

        case Sequence(s1, s2) =>
            val r1 = checkStatement(s1, vars)
            checkStatement(s2, r1)

        case If(conditionExpr, thenStmt, elseStmt) =>
            val conditionType = checkExpressionWithVars(conditionExpr, vars)
            conditionType match {
                case Type(l, Immutable, LocalTypeSuffix(Natives.booleanType)) =>
                    val newImplicitContext = implicitContext glb l
                    (thenStmt, elseStmt) match {
                        case (_: Block, _: Block) =>
                            checkStatement(thenStmt, vars)(
                                implicitly, newImplicitContext, implicitly, implicitly, implicitly)
                            checkStatement(elseStmt, vars)(
                                implicitly, newImplicitContext, implicitly, implicitly, implicitly)
                            vars
                        case _ =>
                            throw TypeError("missing block in if") // TODO
                    }

                case _ =>
                    throw TypeError(s"incorrect type for condition: $conditionType")
            }

        case Let(varId, e) if !vars.contains(varId) =>
            val eType = checkExpressionWithVars(e, vars)
            vars + (varId -> eType)

        case Let(varId, e) if vars.contains(varId) =>
            val varType = vars.getOrElse(varId, throw TypeError(s"undeclared variable $varId"))
            val eType = checkExpressionWithVars(e, vars)
            if (eType !<= varType)
                throw TypeError(s"incompatible type for assignment: $varId ($eType)")
            vars

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

                    //if (fieldType.m == Immutable) // TODO: check if this is ok to remove
                    //    throw TypeError(s"invalid assignment of immutable field: $fieldId (in class $thisType)")

                    if (implicitContext !<= fieldType.l)
                        throw TypeError(s"wrong assignment in implicit context: $fieldType in $implicitContext context")

                    if (operationLevel !<= fieldType.l)
                        throw TypeError(s"wrong assignment in operation context: " +
                            s"$fieldType in $operationLevel context")

                    vars
            }

        case GetField(varId, fieldId) => declarationContext match {
            case TopLevelContext =>
                throw TypeError("cannot resolve 'this' outside of class declaration")

            case MethodContext(thisType, mutabilityContext, operationLevel) =>
                if (vars.contains(varId))
                    throw TypeError(s"operation requires a fresh variable")

                val fieldType = ClassTable.fields(thisType).get(fieldId) match {
                    case Some(value) => value.typ
                    case None => throw TypeError(s"field not found: $fieldId (in class $thisType)")
                }

                vars + (varId -> Type(fieldType.l lub operationLevel,
                    fieldType.m lub mutabilityContext,
                    fieldType.suffix))
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
            vars

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

                    if (implicitContext != methodType.operationLevel)
                        throw TypeError("wrong operation level for implicit context")

                    if (operationLevel != methodType.operationLevel)
                        throw TypeError("wrong operation level for method context")

                    if (mutabilityContext == Immutable)
                        throw TypeError(s"update call in query: $methodId")

            }
            vars

        case CallQuery(varId, recvExpr, methodId, argumentExprs) =>
            if (vars.contains(varId))
                throw TypeError(s"operation requires a fresh variable")

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

            val resType = Type(methodType.returnType.l lub recvType.l,
                methodType.returnType.m,
                methodType.returnType.suffix)

            vars + (varId -> resType) + (resId -> resType)

        case CallQueryThis(varId, methodId, argumentExprs) =>
            if (vars.contains(varId))
                throw TypeError(s"operation requires a fresh variable")

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

                    val resType = Type(methodType.returnType.l lub operationLevel,
                        methodType.returnType.m,
                        methodType.returnType.suffix)

                    vars + (varId -> resType) + (resId -> resType)
            }

        case Replicate(varId, _, classType, constructor, consistency, mutability) =>
            if (vars.contains(varId))
                throw TypeError(s"operation requires a fresh variable")

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

            // TODO well formedness check
            vars + (varId -> Type(consistency, mutability, RefTypeSuffix(classType)))

        case Transaction(body, except) =>
            checkStatement(body, vars)
            checkStatement(except, vars)
            vars

        case Print(expression) =>
            checkExpressionWithVars(expression, vars)
            vars
    }
}
