import lang._

object TypeChecker {

    case class TypeException(s : String) extends Exception(s)

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
        programDecl.classTable.foreach(c => checkClass(c._1, c._2)(programDecl.classTable))
        typeOfExpr(programDecl.body, Map.empty)(null, TopLevelContext, Strong, programDecl.classTable) // TODO
    }

    def checkClass(classDecl : ClassDecl, thisConsistency: ConsistencyType)(implicit classTable : ClassTable) : Unit = {
        for ((methodId, methodDecl) <- classDecl.methods) {
            val varEnv: VarEnv = methodDecl.declaredParameters.map(varDecl => (varDecl.name, varDecl.typ)).toMap
            methodDecl match {
                case q: QueryMethodDecl =>
                    // TODO: using operation level as implicit context is wrong
                    val returnTyp = TypeChecker.typeOfExpr(methodDecl.body, varEnv)((classDecl.asType, thisConsistency), ImmutableContext, q.operationLevel.consistencyType(), classTable)
                    if (!(returnTyp <= q.returnType))
                        throw TypeException(s"return type is wrong. Expected: ${q.returnType}, but was $returnTyp (in method $methodId)")
                case u: UpdateMethodDecl =>
                    // TODO: using operation level as implicit context is wrong
                    val returnTyp = TypeChecker.typeOfExpr(methodDecl.body, varEnv)((classDecl.asType, thisConsistency), MutableContext, u.operationLevel.consistencyType(), classTable).effectiveType()
                    if (returnTyp.baseType != Natives.UNIT_TYPE)
                        throw TypeException(s"return type is wrong. Expected: ${Natives.UNIT_TYPE}, but was $returnTyp (in method $methodId)")
            }
        }
    }


    private def typeOfExpr(expr: IRExpr, vars: VarEnv)(implicit declarationContext: DeclarationContext,
                                                       implicitContext: ConsistencyType,
                                                       classTable: ClassTable): Type = expr match {
        // TODO: consistency of literals
        case Num(_) => CompoundType(NumberType, Local, Bottom)
        case True => CompoundType(BooleanType, Local, Bottom)
        case False => CompoundType(BooleanType, Local, Bottom)
        case UnitLiteral => CompoundType(UnitType, Local, Bottom)

        case Var(id: VarId) => vars.getOrElse(id, throw TypeException("variable not declared: " + id))

        case Let(id: VarId, namedExpr: IRExpr, body: IRExpr) =>
            val namedType = typeOfExpr(namedExpr, vars)
            typeOfExpr(body, vars + (id -> namedType))

        case If(conditionExpr, thenExpr, elseExpr) =>
            val condType = typeOfExpr(conditionExpr, vars).effectiveType()

            if (condType.baseType != BooleanType)
                throw TypeException("condition must be Bool, but was: " + condType)

            val newImplicitContext = implicitContext glb condType.consistencyType

            val t1 = typeOfExpr(thenExpr, vars)(declarationContext, newImplicitContext, classTable)
            val t2 = typeOfExpr(elseExpr, vars)(declarationContext, newImplicitContext, classTable)

            if (t1 != t2) // TODO: use lub for expression type inference instead?
                throw TypeException("branches have diverging types: " + t1 + " and " + t2)

            t1

        case Equals(e1 : IRExpr, e2 : IRExpr) =>
            val t1 = typeOfExpr(e1, vars)
            val t2 = typeOfExpr(e2, vars)

            if (t1 != t2) throw TypeException(s"non-matching types in 'equals': $t1 and $t2")

            val CompoundType(_, c, _) = t1.effectiveType()
            CompoundType(BooleanType, c, Bottom)

        case This =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeException("cannot resolve 'this' outside class")

                case MethodContext((classType, consistencyType), _, _) =>
                    CompoundType(classType, consistencyType, Mutable)
            }

        case GetField(fieldId : FieldId) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeException("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    val classDecl = classTable
                        .getOrElse((thisType._1.classId, thisType._2), throw TypeException("class of 'this' not available: " + thisType))

                    val fieldDecl = classDecl
                        .getField(fieldId).getOrElse(throw TypeException("field not available: " + fieldId + s" (in class $thisType)"))

                    // TODO: add lub with opLevel
                    fieldDecl.typ
            }

        case SetField(fieldId : FieldId, value : IRExpr) =>
            declarationContext match {
                case TopLevelContext =>
                    throw TypeException("cannot resolve 'this' outside class")

                case MethodContext(thisType, mutabilityContext, operationLevel) =>
                    if (mutabilityContext != MutableContext)
                        throw TypeException("assignment in immutable context: " + thisType)

                    val valueType = typeOfExpr(value, vars)
                    val cls = classTable.getOrElse((thisType._1.classId, thisType._2), throw TypeException("class of 'this' not available: " + thisType))
                    val fieldDecl = cls.getField(fieldId).getOrElse(throw TypeException("field not available: " + fieldId + s" (in class $thisType)"))
                    if (!(valueType <= fieldDecl.typ))
                        throw TypeException(s"assignment has wrong type. expected: ${fieldDecl.typ} (but was: ${valueType})")

                    if (fieldDecl.typ.effectiveType().mutabilityType == Immutable)
                        throw TypeException(s"assignment of immutable field")

                    if (!(implicitContext <= fieldDecl.typ.effectiveType().consistencyType))
                        throw TypeException(s"wrong assignment in implicit context: ${fieldDecl.typ} in $implicitContext context")

                    if (!(operationLevel.consistencyType() <= fieldDecl.typ.effectiveType().consistencyType))
                        throw TypeException(s"wrong assignment in operation context: ${fieldDecl.typ} in ${operationLevel.consistencyType()} context")

                    valueType
            }


        case CallQuery(recv, methodId, arguments) =>
            val recvType = typeOfExpr(recv, vars)

            recvType match {
                case CompoundType(recvClassType@ClassType(classId, typeArguments), consistencyType, _) =>

                    val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))
                    val (mthdDecl, typeEnv) = checkMethodCall((recvClassType, consistencyType), methodId, vars, argTypes)

                    val queryDecl = mthdDecl match {
                        case q : QueryMethodDecl => q
                        case _ => throw TypeException(s"expected query method: $methodId")
                    }

                    resolveType(queryDecl.returnTyp, typeEnv)

                case _ => throw TypeException(s"receiver not a class type: " + recv)
            }

        case CallUpdate(recv, methodId, arguments) =>
            val recvType = typeOfExpr(recv, vars)

            recvType match {
                case CompoundType(recvClassType@ClassType(classId, typeArguments), consistencyType, mutabilityType) =>

                    if (mutabilityType == Immutable)
                        throw TypeException(s"update call on immutable receiver")

                    val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))
                    val (mthdDecl, typeEnv) = checkMethodCall((recvClassType, consistencyType), methodId, vars, argTypes)

                    if (!(implicitContext <= mthdDecl.operationLevel.consistencyType()))
                        throw TypeException(s"wrong operation level in context: ${mthdDecl.operationLevel.consistencyType()} in $implicitContext")

                    val updateDecl = mthdDecl match {
                        case u: UpdateMethodDecl => u
                        case _ => throw TypeException(s"expected update method: $methodId")
                    }

                    CompoundType(Natives.UNIT_TYPE, Strong, Bottom) // TODO: consistency of unit

                case _ => throw TypeException(s"receiver not a class type: " + recv)
            }

        case Sequence(exprs) =>
            exprs.foldLeft(null: Type)((r, e) => typeOfExpr(e, vars))

        case New(classId, typeArgs, consistencyType) =>
            val classDecl = classTable.getOrElse((classId, consistencyType), throw TypeException(s"class not available: $consistencyType $classId"))
            if (typeArgs.length != classDecl.typeParameters.length) throw TypeException(s"wrong number of type arguments: " + classId)
            (typeArgs zip classDecl.typeParameters).foreach(e => {
                val (arg, param) = e
                if (!(arg.effectiveType() <= param.effectiveType())) throw TypeException(s"wrong type argument for type variable: $arg (expected: $param)")
            })

            CompoundType(ClassType(classId, typeArgs), consistencyType, Bottom)

        case _ => ???
    }

    private def checkMethodCall(recvType : (ClassType, ConsistencyType), methodId : MethodId, vars : VarEnv, argTypes : Seq[Type])
                               (implicit thisType : (ClassType, ConsistencyType), mutableContext : M, classTable : ClassTable) : (MethodDecl, TypeEnv) = {

        val recvClassDecl = classTable.getOrElse((recvType._1.classId, recvType._2), throw TypeException("class not available: " + recvType))

        if (recvClassDecl.typeParameters.length != recvType._1.typeArguments.length)
            throw TypeException(s"wrong number of type arguments: " + recvType)

        val typeEnv : TypeEnv =
            recvClassDecl.typeParameters.zip(recvType._1.typeArguments).map(p => (p._1.typeVarId, p._2)).toMap

        val methodDecl : MethodDecl = recvClassDecl
            .getMethod(methodId).getOrElse(throw TypeException("method not available: " + methodId + s" (in class $thisType)"))

        if (argTypes.size != methodDecl.declaredParameters.size)
            throw TypeException(s"wrong number of arguments for method $methodId: ${argTypes.size} (expected: ${methodDecl.declaredParameters.size}")

        argTypes.zip(methodDecl.declaredParameterTypes).foreach(t => {
            val argType = t._1
            val parameterType = resolveType(t._2, typeEnv)
            if (!(argType <= parameterType))
                throw TypeException(s"wrong argument type for method $methodId: $argType (expected: $parameterType)")
        })

        (methodDecl, typeEnv)
    }
}
