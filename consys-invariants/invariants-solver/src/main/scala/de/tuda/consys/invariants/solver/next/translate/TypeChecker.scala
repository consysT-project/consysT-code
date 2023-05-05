package de.tuda.consys.invariants.solver.next.translate

import de.tuda.consys.invariants.solver.next.ir.IR._
import de.tuda.consys.invariants.solver.next.ir.Natives

object TypeChecker {

  case class TypeException(s : String) extends Exception(s)

  trait M {
    def union(other : M) : M
  }
  case object Immutable extends M {
    override def union(other : M) : M = other
  }
  case object Mutable extends M {
    override def union(other : M) : M = Mutable
  }

  type VarEnv = Map[VarId, Type]
  type TypeEnv = Map[TypeVarId, Type]


  def resolveType(typ : Type, typeVars : TypeEnv) : Type = typ match {
    case TypeVar(x) => typeVars.getOrElse(x, throw TypeException(s"type variable not declared: " + x))
    case ClassType(classId, typeArgs) =>
      ClassType(classId, typeArgs.map(arg => resolveType(arg, typeVars)))
  }

  def checkClass(classDecl : ClassDecl[_])(implicit classTable : ClassTable) : Unit = classDecl match {
    case ObjectClassDecl(name, typeParameters, invariant, fields, methods) =>

      val invariantType = TypeChecker.typeOfExpr(invariant, Map())(classDecl.asType, Immutable, classTable)
      if (invariantType != Natives.BOOL_TYPE)
        throw TypeException(s"invariant is not Bool, but: " + invariantType)

      for ((methodId, methodDecl) <- methods) {
        val varEnv : VarEnv = methodDecl.declaredParameters.map(varDecl => (varDecl.name, varDecl.typ)).toMap
        methodDecl match {
          case q : QueryMethodDecl =>
            val returnTyp = TypeChecker.typeOfExpr(methodDecl.body, varEnv)(classDecl.asType, Immutable, classTable)
            if (returnTyp != q.returnTyp)
              throw TypeException(s"return type is wrong. Expected: ${q.returnTyp}, but was $returnTyp (in method $methodId)")
          case _ : UpdateMethodDecl =>
            val returnTyp = TypeChecker.typeOfExpr(methodDecl.body, varEnv)(classDecl.asType, Mutable, classTable)
            if (returnTyp != Natives.UNIT_TYPE)
              throw TypeException(s"return type is wrong. Expected: ${Natives.UNIT_TYPE}, but was $returnTyp (in method $methodId)")
        }
      }

    case NativeClassDecl(name, typeVars, sort, methods) =>
      // Native classes are expected to be fine
  }


  def typeOfExpr(expr : IRExpr, vars : VarEnv)(implicit thisType : ClassType, mutableContext : M, classTable : ClassTable) : Type = expr match {
    case Num(n : Int) => Natives.INT_TYPE
    case True => Natives.BOOL_TYPE
    case False => Natives.BOOL_TYPE
    case Str(s : String) => Natives.STRING_TYPE
    case UnitLiteral => Natives.UNIT_TYPE

    case Var(id : VarId) => vars.getOrElse(id, throw TypeException("variable not declared: " + id))

    case Let(id : VarId, namedExpr : IRExpr, body : IRExpr) =>
      val namedType = typeOfExpr(namedExpr, vars)
      typeOfExpr(body, vars + (id -> namedType))

    case If(conditionExpr, thenExpr, elseExpr) =>
      val condType = typeOfExpr(conditionExpr, vars)

      if (condType != Natives.BOOL_TYPE)
        throw TypeException("condition must be Bool, but was: " + condType)

      // In the branches of the if, state changes are not allowed as we do not know which changes to apply
      val t1 = typeOfExpr(thenExpr, vars)(thisType, Immutable, classTable)
      val t2 = typeOfExpr(elseExpr, vars)(thisType, Immutable, classTable)

      if (t1 != t2)
        throw TypeException("branches have diverging types: " + t1 + " and " + t2)

      t1


    case Equals(e1 : IRExpr, e2 : IRExpr) =>
      val t1 = typeOfExpr(e1, vars)
      val t2 = typeOfExpr(e2, vars)

      if (t1 != t2) throw TypeException(s"non-matching types in 'equals': $t1 and $t2")

      Natives.BOOL_TYPE

    case This =>
      thisType

    case GetField(fieldId : FieldId) =>
      val classDecl = classTable
        .getOrElse(thisType.classId, throw TypeException("class of 'this' not available: " + thisType))

      val fieldDecl = classDecl
        .getField(fieldId).getOrElse(throw TypeException("field not available: " + fieldId + s" (in class $thisType)"))

      fieldDecl.typ


    case SetField (fieldId : FieldId, value : IRExpr) =>
      if (mutableContext != Mutable) throw TypeException("assignment in immutable context: " + thisType)

      val valueType = typeOfExpr(value, vars)
      val cls = classTable.getOrElse(thisType.classId, throw TypeException("class of 'this' not available: " + thisType))
      val fieldDecl = cls.getField(fieldId).getOrElse(throw TypeException("field not available: " + fieldId + s" (in class $thisType)"))
      if (valueType != fieldDecl.typ)
        throw TypeException(s"assignment has wrong type. expected: ${fieldDecl.typ} (but was: ${valueType})")

      valueType



    case CallQuery(recv, methodId, arguments) =>
      val recvType = typeOfExpr(recv, vars)

      recvType match {
        case recvClassType@ClassType(classId, typeArguments) =>

          val (mthdDecl, typeEnv) = checkMethodCall(recvClassType, methodId, vars, arguments)

          val queryDecl = mthdDecl match {
            case q : QueryMethodDecl => q
            case _ => throw TypeException(s"expected query method: $methodId")
          }

          resolveType(queryDecl.returnTyp, typeEnv)

        case _ => throw TypeException(s"receiver not a class type: " + recv)
      }




    case CallUpdateThis(methodId, arguments) =>
      if (mutableContext != Mutable)
        throw TypeException(s"cannot call update on immutable type: $methodId")

      val (mthdDecl, _) = checkMethodCall(thisType, methodId, vars, arguments)

      val updateDecl = mthdDecl match {
        case u : UpdateMethodDecl => u
        case _ => throw TypeException(s"expected update method: $methodId")
      }

      Natives.UNIT_TYPE


    case CallUpdateField(fieldId, methodId, arguments) =>
      if (mutableContext != Mutable)
        throw TypeException(s"cannot call update on immutable type: $methodId")

      val thisClass = classTable.getOrElse(thisType.classId, throw TypeException("class not available: " + thisType))
      val fieldDecl = thisClass.getField(fieldId).getOrElse(throw TypeException(s"field not available: $fieldId (in class ${thisClass.classId}) )"))

      fieldDecl.typ match {
        case fieldClassType@ClassType(classId, typeArguments) =>
          val (mthdDecl, _) = checkMethodCall(fieldClassType, methodId, vars, arguments)

          val updateDecl = mthdDecl match {
            case u : UpdateMethodDecl => u
            case _ => throw TypeException(s"expected update method: $methodId")
          }

          Natives.UNIT_TYPE

        case _ => throw TypeException(s"expected class type, but got: " + fieldDecl.typ)
      }


  }

  private def checkMethodCall(recvType : ClassType, methodId : MethodId, vars : VarEnv, arguments : Seq[IRExpr])
                             (implicit thisType : ClassType, mutableContext : M, classTable : ClassTable) : (MethodDecl, TypeEnv) = {

    val recvClassDecl = classTable.getOrElse(recvType.classId, throw TypeException("class not available: " + thisType))

    if (recvClassDecl.typeParameters.length != recvType.typeArguments.length)
      throw TypeException(s"wrong number of type arguments: " + recvType)

    val typeEnv : TypeEnv =
      recvClassDecl.typeParameters.zip(recvType.typeArguments).map(p => (p._1.typeVarId, p._2)).toMap

    val methodDecl : MethodDecl = recvClassDecl
      .getMethod(methodId).getOrElse(throw TypeException("method not available: " + methodId + s" (in class $thisType)"))

    if (arguments.size != methodDecl.declaredParameters.size)
      throw TypeException(s"wrong number of arguments for method $methodId: ${arguments.size} (expected: ${methodDecl.declaredParameters.size}")

    val argTypes = arguments.map(argExpr => typeOfExpr(argExpr, vars))

    argTypes.zip(methodDecl.declaredParameterTypes).foreach(t => {
      val argType = t._1
      val parameterType = resolveType(t._2, typeEnv)
      if (argType != parameterType)
        throw TypeException(s"wrong argument type for method $methodId: $argType (expected: $parameterType)")
    })

    (methodDecl, typeEnv)

  }

}
