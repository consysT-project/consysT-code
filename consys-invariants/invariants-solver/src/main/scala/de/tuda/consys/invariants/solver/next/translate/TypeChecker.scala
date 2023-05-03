package de.tuda.consys.invariants.solver.next.translate

import de.tuda.consys.invariants.solver.next.ir.IR._
import de.tuda.consys.invariants.solver.next.ir.Natives

object TypeChecker {

  case class TypeException(s : String) extends Exception(s)

  trait M
  case object Immutable extends M
  case object Mutable extends M

  type T = (Type, M)

  def checkCls(cls : ClassDecl)(implicit classTable : Map[ClassId, ClassDecl]) : Unit = cls match {
    case ObjectClassDecl(name, invariant, fields, methods) =>
      val invariantType = TypeChecker.checkExpr(invariant, Map())((cls.toType, Immutable), classTable)
      if (invariantType._1 != Natives.BOOL_TYPE)
        throw TypeException(s"invariant is not Bool, but: " + invariantType._1)

      for ((mthdId, mthd) <- methods) {
        val varEnv = mthd.declaredParameters.map(varDecl => (varDecl.name, (varDecl.typ, Immutable))).toMap
        mthd match {
          case _ : QueryDecl =>
            TypeChecker.checkExpr(mthd.body, varEnv)((cls.toType, Immutable), classTable)
          case _ : UpdateDecl =>
            TypeChecker.checkExpr(mthd.body, varEnv)((cls.toType, Mutable), classTable)
        }
      }

    case NativeClassDecl(name) =>
      // Native classes are expected to be fine
  }


  def checkExpr(expr : IRExpr, vars : Map[VarId, T])(implicit thisType : (Type, M), classTable : Map[ClassId, ClassDecl]) : T = expr match {
    case Num(n : Int) => (Natives.INT_TYPE, Mutable)
    case True => (Natives.BOOL_TYPE, Mutable)
    case False => (Natives.BOOL_TYPE, Mutable)
    case Str(s : String) => (Natives.STRING_TYPE, Mutable)

    case Var(id : VarId) => vars.getOrElse(id, throw TypeException("variable not declared: " + id))
    case Let(id : VarId, namedExpr : IRExpr, body : IRExpr) =>
      val namedType = checkExpr(namedExpr, vars)
      checkExpr(body, vars + (id -> namedType))

    case Equals(e1 : IRExpr, e2 : IRExpr) =>
      val (t1, m1) = checkExpr(e1, vars)
      val (t2, m2) = checkExpr(e2, vars)

      if (t1 != t2) throw TypeException(s"non-matching types in 'equals': $t1 and $t2")

      (Natives.BOOL_TYPE, Mutable)

    case This =>
      thisType

    case GetField(id : FieldId) =>
      val cls = classTable.getOrElse(thisType._1.name, throw TypeException("class of 'this' not available: " + thisType))

      cls match {
        case NativeClassDecl(name) => throw TypeException("native class has no fields: " + thisType)
        case ObjectClassDecl(name, invariant, fields, methods) =>
          val fieldDecl = fields.getOrElse(id, throw TypeException("field not available: " + id + s" (in class $thisType)"))
          (fieldDecl.typ, thisType._2)
      }

    case SetField (id : FieldId, value : IRExpr) =>
      if (thisType._2 == Immutable)
        throw TypeException("assignment to immutable object: " + thisType)

      val valueType = checkExpr(value, vars)

      val cls = classTable.getOrElse(thisType._1.name, throw TypeException("class of 'this' not available: " + thisType))

      cls match {
        case NativeClassDecl(name) => throw TypeException("native class has no fields: " + thisType)
        case ObjectClassDecl(name, invariant, fields, methods) =>
          val fieldDecl = fields.getOrElse(id, throw TypeException("field not available: " + id + s" (in class $thisType)"))

          if (valueType._1 != fieldDecl.typ)
            throw TypeException(s"assignment has wrong type. expected: ${fieldDecl.typ} (but was: ${valueType._1})")

          valueType
      }

    case CallQuery(recv : IRExpr, mthd : MethodId, arguments : Seq[IRExpr] ) =>
      val recvType = checkExpr(recv, vars)
      val argTypes = arguments.map(argExpr => checkExpr(argExpr, vars))

      val cls = classTable.getOrElse(recvType._1.name, throw TypeException("class not available: " + thisType))

      cls match {
        case NativeClassDecl(name) => throw TypeException("native class has no methods: " + thisType)
        case ObjectClassDecl(name, invariant, fields, methods) =>
          val methodDecl: MethodDecl = methods.getOrElse(mthd, throw TypeException("methods not available: " + mthd + s" (in class $thisType)"))

          val queryDecl = methodDecl match {
            case q : QueryDecl => q
            case _ => throw TypeException(s"expected query method: $mthd")
          }

          if (argTypes.size != methodDecl.declaredParameters.size)
            throw TypeException(s"wrong number of arguments for method $mthd: ${argTypes.size} (expected: ${methodDecl.declaredParameters.size}")

          argTypes.zip(methodDecl.declaredParameterTypes).foreach(t => {
            val argType = t._1._1
            val expectedType = t._2
            if (argType != expectedType)
              throw TypeException(s"wrong argument type for method $mthd: $argType (expected: $expectedType)")
          })

          (queryDecl.returnTyp, Immutable)
      }

    case CallUpdate(recv : IRExpr, mthd : MethodId, arguments : Seq[IRExpr]) =>
      val recvType = checkExpr(recv, vars)

      if (recvType._2 == Immutable)
        throw TypeException(s"cannot call update on immutable type: $mthd")

      val argTypes = arguments.map(argExpr => checkExpr(argExpr, vars))

      val cls = classTable.getOrElse(recvType._1.name, throw TypeException("class not available: " + thisType))

      cls match {
        case NativeClassDecl(name) => throw TypeException("native class has no methods: " + thisType)
        case ObjectClassDecl(name, invariant, fields, methods) =>
          val methodDecl : MethodDecl = methods.getOrElse(mthd, throw TypeException("methods not available: " + mthd + s" (in class $thisType)"))

          val updateDecl = methodDecl match {
            case u : UpdateDecl => u
            case _ => throw TypeException(s"expected update method: $mthd")
          }

          if (argTypes.size != methodDecl.declaredParameters.size)
            throw TypeException(s"wrong number of arguments for method $mthd: ${argTypes.size} (expected: ${methodDecl.declaredParameters.size}")

          argTypes.zip(methodDecl.declaredParameterTypes).foreach(t => {
            val argType = t._1._1
            val expectedType = t._2
            if (argType != expectedType)
              throw TypeException(s"wrong argument type for method $mthd: $argType (expected: $expectedType)")
          })

          (Natives.INT_TYPE, Immutable)
      }


  }

}
