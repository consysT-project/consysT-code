package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang.ClassTable.{ClassTable, mType}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.TypeError
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.types._

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
        classDecl.methods.foreachEntry((_, methodDecl) => {
            val typeVarEnv: TypeVarEnv = classDecl.typeParametersToEnv
            methodDecl match {
                case m: QueryMethodDecl =>
                    checkQuery(m, typeVarEnv, classDecl.toType)
                case u: UpdateMethodDecl =>
                    checkUpdate(u, typeVarEnv, classDecl.toType)
            }
        })
    }

    private def checkUpdate(method: UpdateMethodDecl,
                            typeVars: TypeVarEnv,
                            thisType: ClassType)(implicit classTable: ClassTable): Unit = {
        val methodType = UpdateType(method.operationLevel, method.declaredParameters.map(x => x.typ))
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override: ${method.name}")

        val varEnv = method.declaredParametersToEnvironment
        checkStatement(method.body, varEnv)(
            MethodContext(thisType, MutableContext, method.operationLevel), Local, classTable, typeVars)
    }

    private def checkQuery(method: QueryMethodDecl,
                           typeVars: TypeVarEnv,
                           thisType: ClassType)(implicit classTable: ClassTable): Unit = {
        val methodType = QueryType(method.operationLevel, method.declaredParameters.map(x => x.typ), method.returnType)
        if (!checkOverride(method.name, thisType, methodType))
            throw TypeError(s"invalid update override: ${method.name}")

        val varEnv = method.declaredParametersToEnvironment
        checkStatement(method.body, varEnv)(
            MethodContext(thisType, ImmutableContext, method.operationLevel), Local, classTable, typeVars)
    }

    private def checkOverride(id: MethodId, receiver: ClassType, typ: MethodType): Boolean = {
        true // TODO
    }

    private def typeOfExpr(expr: Expression, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                           implicitContext: ConsistencyType,
                                                           classTable: ClassTable,
                                                           typeVars: TypeVarEnv): Type = expr match {
        case True =>
            CompoundClassType(Natives.booleanType, Local, Immutable)

        case False =>
            CompoundClassType(Natives.booleanType, Local, Immutable)

        case UnitLiteral =>
            CompoundClassType(Natives.unitType, Local, Immutable)

        case Num(_) =>
            CompoundClassType(Natives.numberType, Local, Immutable)

        case Var(id: VarId) =>
            vars.getOrElse(id, throw TypeError(s"variable not declared: $id"))

        case This =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeError("cannot resolve 'this' outside of class declaration")

                case MethodContext(classType, _, _) =>
                    ???
            }

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

        case ValueExpr(_) => throw TypeError("<ValueExpr> is invalid")
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
            val methodType = mType(methodId, recvType) match {
                case q: QueryType => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            if (argumentExprs.size != methodType.parameters.size)
                throw TypeError(s"wrong number of arguments for method $methodId: ${argumentExprs.size}")

            val argTypes = argumentExprs.map(argExpr => typeOfExpr(argExpr, vars))
            if ((argTypes zip methodType.parameters).forall(x => x._1 <= x._2))
                throw TypeError(s"wrong argument type")
            // TODO: adapt type prefix
            methodType.returnType

        case rhsReplicate(location, classId, consistencyArguments, typeArguments, constructor, consistency, mutability) =>
            val decl = classTable.getOrElse(classId, throw TypeError(s"class not found: $classId"))
            if (decl.typeParameters.size != typeArguments.size)
                throw TypeError(s"wrong number of type arguments")
            if (decl.fields.size != constructor.size)
                throw TypeError(s"wrong number of constructor arguments")

            val constructorTypes = constructor.map(e => typeOfExpr(e, vars))
            (constructorTypes zip decl.fields.values.map(_.typ)).forall(p => p._1 <= p._2)
            // TODO: concrete type parameters?
            RefType(ClassType(classId, consistencyArguments, typeArguments), consistency, mutability)

        case rhsLookup(location, classId, consistencyArguments, typeArguments, consistency, mutability) =>
            RefType(ClassType(classId, consistencyArguments, typeArguments), consistency, mutability)

        case rhsValue(_) => throw TypeError("<rhsValue> is invalid")
    }

    private def checkStatement(statement: Statement, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                                   implicitContext: ConsistencyType,
                                                                   classTable: ClassTable,
                                                                   typeVars: TypeVarEnv): VarEnv = statement match {
        case Skip =>
            vars

        case Error =>
            vars

        case Block(s) =>
            checkStatement(s, vars)
            vars

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
            vars + (varId -> namedType)

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
                        throw TypeError(s"wrong assignment in operation context: " +
                            s"${fieldDecl.typ} in ${operationLevel.consistencyType()} context")

                    vars
            }

        case CallUpdate(recvExpr, methodId, arguments) =>
            val recvType = bound(typeOfExpr(recvExpr, vars))
            if (recvType.mutabilityType == Immutable)
                throw TypeError(s"invalid update call on immutable receiver: " +
                    s"$methodId (in class ${recvType.classType.classId})")

            val methodType = mType(methodId, recvType) match {
                case q: QueryType => q
                case _ => throw TypeError(s"expected query method: $methodId")
            }

            if (arguments.size != methodType.parameters.size)
                throw TypeError(s"wrong number of arguments for method $methodId: ${arguments.size}")

            val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))
            if ((argTypes zip methodType.parameters).forall(x => x._1 <= x._2))
                throw TypeError(s"wrong argument type")

            declarationContext match {
                case TopLevelContext =>
                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (operationLevel.consistencyType() !<= methodType.operationLevel.consistencyType())
                        throw TypeError(s"wrong operation level in method context: " +
                            s"${methodType.operationLevel.consistencyType()} in $operationLevel")
                    mutabilityContext match {
                        case ImmutableContext => throw TypeError(s"update call in query: ${methodId}")
                        case MutableContext =>
                    }
            }

            if (!(implicitContext <= methodType.operationLevel.consistencyType()))
                throw TypeError(s"wrong operation level in context: " +
                    s"${methodType.operationLevel.consistencyType()} in $implicitContext")

            vars

        case Transaction(body, except) =>
            checkStatement(body, vars)
            checkStatement(except, vars)
            vars
    }
}
