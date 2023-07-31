package de.tuda.consys.invariants.solver.next.translate.types


import de.tuda.consys.invariants.solver.next.ir.Classes._
import de.tuda.consys.invariants.solver.next.ir.{ClassTable, Expressions, Natives}
import de.tuda.consys.invariants.solver.next.ir.Types.{ClassType, Type, resolveType}
import Expressions._
import de.tuda.consys.invariants.solver.next.translate.types.Mutability.{Immutable, M, Mutable}


object TypeChecker {

  type VarEnv = Map[VarId, Type]
  type TypeEnv = Map[TypeVarId, Type]


  def typedClassOf[Lang <: BaseExpressions with BaseNumExpressions with BaseBoolExpressions with BaseStringExpressions with BaseObjectExpressions]
  (classDecl : ObjectClassDecl[Lang#Expr])(implicit classTable : ClassTable[Lang#Expr]) : ObjectClassDecl[TypedLang.Expr] = {
      val invariantTExpr = typedExprOf(classDecl.invariant, Map())(classDecl.asType, Immutable, classTable)

      if (invariantTExpr.typ != Natives.BOOL_TYPE)
        throw TypeException(s"invariant is not Bool, but: " + invariantTExpr)

      val builder = Map.newBuilder[MethodId, ObjectMethodDecl[TypedLang.Expr]]

      for ((methodId, methodDecl) <- classDecl.methods) {
        val varEnv : VarEnv = methodDecl.declaredParameters.map(varDecl => (varDecl.name, varDecl.typ)).toMap
        methodDecl match {

          case queryMethodDecl : QueryMethodDecl =>
            val bodyTExpr = typedExprOf(methodDecl.body, varEnv)(classDecl.asType, Immutable, classTable)

            if (bodyTExpr.typ != queryMethodDecl.returnTyp)
              throw TypeException(s"return type is wrong. Expected: ${queryMethodDecl.returnTyp}, but was ${bodyTExpr.typ} (in method $methodId)")

            builder.addOne((queryMethodDecl.name, ObjectQueryMethodDecl(queryMethodDecl.name, queryMethodDecl.declaredParameters, queryMethodDecl.returnTyp, bodyTExpr)))

          case updateMethodDecl : UpdateMethodDecl =>
            val bodyTExpr = typedExprOf(methodDecl.body, varEnv)(classDecl.asType, Mutable, classTable)
            if (bodyTExpr.typ != Natives.UNIT_TYPE)
              throw TypeException(s"return type is wrong. Expected: ${Natives.UNIT_TYPE}, but was ${bodyTExpr.typ} (in method $methodId)")

            builder.addOne((updateMethodDecl.name, ObjectUpdateMethodDecl(updateMethodDecl.name, updateMethodDecl.declaredParameters, bodyTExpr)))
        }
      }

    ObjectClassDecl(
      classDecl.classId,
      classDecl.typeParameters,
      invariantTExpr,
      classDecl.fields,
      builder.result()
    )
  }

  def typedExprOf[Lang <: BaseExpressions with BaseNumExpressions with BaseBoolExpressions with BaseStringExpressions with BaseObjectExpressions]
  (expr : Lang#Expr, vars : VarEnv)(implicit thisType : ClassType, mutableContext : M, classTable : ClassTable[Lang#Expr]) : TypedLang.Expr = expr match {
    case numExpr : Lang#BaseNum => TypedLang.IRNum(numExpr.value, Natives.INT_TYPE)
    case trueExpr : Lang#BaseTrue => TypedLang.IRTrue(Natives.BOOL_TYPE)
    case falseExpr : Lang#BaseFalse => TypedLang.IRFalse(Natives.BOOL_TYPE)
    case stringExpr : Lang#BaseString => TypedLang.IRString(stringExpr.value, Natives.STRING_TYPE)
    case unitExpr : Lang#BaseUnit => TypedLang.IRUnit(Natives.UNIT_TYPE)

    case varExpr : Lang#BaseVar =>
      val varTyp = vars.getOrElse(varExpr.id, throw TypeException("variable not declared: " + varExpr.id))
      TypedLang.IRVar(varExpr.id, varTyp)

    case letExpr : Lang#BaseLet =>
      val namedTExpr = typedExprOf(letExpr.namedExpr, vars)
      val bodyTExpr = typedExprOf(letExpr.bodyExpr, vars + (letExpr.id -> namedTExpr.typ))
      TypedLang.IRLet(letExpr.id, namedTExpr, bodyTExpr, bodyTExpr.typ)

    case ifExpr : Lang#BaseIf =>
      val condTExpr = typedExprOf(ifExpr.conditionExpr, vars)

      if (condTExpr.typ != Natives.BOOL_TYPE)
        throw TypeException("condition must be Bool, but was: " + condTExpr.typ)

      // In the branches of the if, state changes are not allowed as we do not know which changes to apply
      val thenTExpr = typedExprOf(ifExpr.thenExpr, vars)(thisType, Immutable, classTable)
      val elseTExpr = typedExprOf(ifExpr.elseExpr, vars)(thisType, Immutable, classTable)

      if (thenTExpr.typ != elseTExpr.typ)
        throw TypeException("branches have diverging types: " + thenTExpr + " and " + elseTExpr)

      TypedLang.IRIf(condTExpr, thenTExpr, elseTExpr, thenTExpr.typ)


    case equalsExpr : Lang#BaseEquals =>
      val tExpr1 = typedExprOf(equalsExpr.expr1, vars)
      val tExpr2 = typedExprOf(equalsExpr.expr2, vars)

      if (tExpr1.typ != tExpr2.typ) throw TypeException(s"non-matching types in 'equals': ${tExpr1.typ} and ${tExpr2.typ}")

      TypedLang.IREquals(tExpr1, tExpr2, Natives.BOOL_TYPE)

    case thisExpr : Lang#BaseThis =>
      TypedLang.IRThis(thisType)

    case newExpr : Lang#BaseNew =>
      val classId = newExpr.classId

      val classDecl = classTable
        .getOrElse(classId, throw TypeException("class not available: " + classId))

      classDecl match {
        case objClassDecl @ ObjectClassDecl(_, typeParameters, invariant, fields, methods) =>
          if (newExpr.typeArguments.length != typeParameters.length)
            throw TypeException(s"wrong number of type parameters for $classId: ${newExpr.typeArguments.length} (but required: ${typeParameters.length})" )

          if (newExpr.arguments.keySet != fields.keySet)
            throw TypeException(s"fields do not match for $classId")

          val argTExprs = newExpr.arguments.map(entry => (entry._1, typedExprOf(entry._2, vars)))

          val typeEnv : TypeEnv = typeParameters.map(typeVar => typeVar.typeVarId).zip(newExpr.typeArguments).toMap

          for (field <- fields) {
            val arg = argTExprs.getOrElse(field._1, throw new TypeException("TODO: THIS SHOULD NOT HAPPEN!"))
            val resolvedFieldType = resolveType(field._2.typ, typeEnv)

            if (resolvedFieldType != arg.typ)
              throw TypeException(s"argument type does not match field ${field._1}: ${arg.typ} (but required: ${resolvedFieldType})")

          }

          val typ = objClassDecl.toType(newExpr.typeArguments)
          TypedLang.IRNew(classId, newExpr.typeArguments, argTExprs, typ)


        case NativeClassDecl(classId, typeParameters, sortImpl, methods) =>
          //TODO: Constructor for native class decl
        throw TypeException("constructor not available for native class: " + classId)
      }


    case getFieldExpr : Lang#BaseGetField =>
      val fieldId = getFieldExpr.fieldId

      val classDecl = classTable
        .getOrElse(thisType.classId, throw TypeException("class of 'this' not available: " + thisType))

      val fieldDecl = classDecl
        .getField(fieldId).getOrElse(throw TypeException(s"field not available: $fieldId (in class $thisType)"))

      TypedLang.IRGetField(fieldId, fieldDecl.typ)


    case setFieldExpr : Lang#BaseSetField =>
      if (mutableContext != Mutable) throw TypeException("assignment in immutable context: " + thisType)

      val fieldId = setFieldExpr.fieldId

      val valueTExpr = typedExprOf(setFieldExpr.newValue, vars)
      val cls = classTable.getOrElse(thisType.classId, throw TypeException("class of 'this' not available: " + thisType))
      val fieldDecl = cls.getField(fieldId).getOrElse(throw TypeException("field not available: " + fieldId + s" (in class $thisType)"))
      if (valueTExpr.typ != fieldDecl.typ)
        throw TypeException(s"assignment has wrong type. expected: ${fieldDecl.typ} (but was: ${valueTExpr.typ})")

      TypedLang.IRSetField(fieldId, valueTExpr, valueTExpr.typ)


    case callQueryExpr : Lang#BaseCallQuery =>
      val recvTExpr = typedExprOf(callQueryExpr.recv, vars)

      val methodId = callQueryExpr.methodId

      recvTExpr.typ match {
        case recvClassType@ClassType(classId, typeArguments) =>

          val (mthdDecl, typeEnv, argTExprs) = typeCheckMethodCall(recvClassType, methodId, vars, callQueryExpr.arguments)

          val queryDecl = mthdDecl match {
            case q : QueryMethodDecl => q
            case _ => throw TypeException(s"expected query method: $methodId")
          }

          TypedLang.IRCallQuery(recvTExpr, methodId, argTExprs, resolveType(queryDecl.returnTyp, typeEnv))

        case _ => throw TypeException(s"receiver not a class type: " + callQueryExpr.recv)
      }


    case callUpdateThisExpr : Lang#BaseCallUpdateThis =>
      val methodId = callUpdateThisExpr.methodId

      if (mutableContext != Mutable)
        throw TypeException(s"cannot call update on immutable type: $methodId")

      val (mthdDecl, _, argTExprs) = typeCheckMethodCall(thisType, methodId, vars, callUpdateThisExpr.arguments)

      val updateDecl = mthdDecl match {
        case u : UpdateMethodDecl => u
        case _ => throw TypeException(s"expected update method: $methodId")
      }

      TypedLang.IRCallUpdateThis(methodId, argTExprs, Natives.UNIT_TYPE)



    case callUpdateFieldExpr : Lang#BaseCallUpdateField =>
      val methodId = callUpdateFieldExpr.methodId
      val fieldId = callUpdateFieldExpr.fieldId

      if (mutableContext != Mutable)
        throw TypeException(s"cannot call update on immutable type: $methodId")

      val thisClass = classTable.getOrElse(thisType.classId, throw TypeException("class not available: " + thisType))
      val fieldDecl = thisClass.getField(fieldId).getOrElse(throw TypeException(s"field not available: $fieldId (in class ${thisClass.classId}) )"))

      fieldDecl.typ match {
        case fieldClassType@ClassType(classId, typeArguments) =>
          val (mthdDecl, _, argTExprs) = typeCheckMethodCall(fieldClassType, methodId, vars, callUpdateFieldExpr.arguments)

          val updateDecl = mthdDecl match {
            case u : UpdateMethodDecl => u
            case _ => throw TypeException(s"expected update method: $methodId")
          }

          TypedLang.IRCallUpdateField(fieldId, methodId, argTExprs, Natives.UNIT_TYPE)

        case _ => throw TypeException(s"expected class type, but got: " + fieldDecl.typ)
      }
  }

  private def typeCheckMethodCall[Lang <: BaseExpressions with BaseNumExpressions with BaseBoolExpressions with BaseStringExpressions with BaseObjectExpressions]
    (recvType : ClassType, methodId : MethodId, vars : VarEnv, arguments : Seq[Lang#Expr])
                             (implicit thisType : ClassType, mutableContext : M, classTable : ClassTable[Lang#Expr]) : (MethodDecl, TypeEnv, Seq[TypedLang.Expr]) = {

    val recvClassDecl = classTable.getOrElse(recvType.classId, throw TypeException("class not available: " + thisType))

    if (recvClassDecl.typeParameters.length != recvType.typeArguments.length)
      throw TypeException(s"wrong number of type arguments: " + recvType)

    val typeEnv : TypeEnv =
      recvClassDecl.typeParameters.zip(recvType.typeArguments).map(p => (p._1.typeVarId, p._2)).toMap

    val methodDecl : MethodDecl = recvClassDecl
      .getMethod(methodId).getOrElse(throw TypeException("method not available: " + methodId + s" (in class $thisType)"))

    if (arguments.size != methodDecl.declaredParameters.size)
      throw TypeException(s"wrong number of arguments for method $methodId: ${arguments.size} (expected: ${methodDecl.declaredParameters.size}")

    val argTExprs = arguments.map(argExpr => typedExprOf(argExpr, vars))

    argTExprs.zip(methodDecl.declaredParameterTypes).foreach(t => {
      val argType = t._1.typ
      val parameterType = resolveType(t._2, typeEnv)
      if (argType != parameterType)
        throw TypeException(s"wrong argument type for method $methodId: $argType (expected: $parameterType)")
    })

    (methodDecl, typeEnv, argTExprs)

  }

}
