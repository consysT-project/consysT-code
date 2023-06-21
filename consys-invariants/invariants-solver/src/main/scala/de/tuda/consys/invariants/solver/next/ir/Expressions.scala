package de.tuda.consys.invariants.solver.next.ir

import de.tuda.consys.invariants.solver.next.ir.IR.{FieldId, MethodId, Type, VarId}

object Expressions {

  sealed trait IRExpr
  sealed trait IRLiteral extends IRExpr

  sealed trait IRMethodCall extends IRExpr {
    def arguments : Seq[IRExpr]
    def methodId : MethodId
  }

  trait TypedExpr {
    def typ : Type
  }

  trait IRNum extends IRLiteral {
    def value : Int
  }
  trait IRTrue extends IRLiteral
  trait IRFalse extends IRLiteral
  trait IRString extends IRLiteral {
    def value : String
  }
  trait IRUnit extends IRLiteral


  trait IRVar extends IRExpr {
    def id : VarId
  }
  trait IRLet extends IRExpr {
    def id : VarId
    def namedExpr : IRExpr
    def body : IRExpr
  }
  trait IRIf extends IRExpr {
    def conditionExpr : IRExpr
    def thenExpr : IRExpr
    def elseExpr : IRExpr
  }
  trait IREquals extends IRExpr {
    def expr1 : IRExpr
    def expr2 : IRExpr
  }
  trait IRThis extends IRExpr
  trait IRGetField extends IRExpr {
    def fieldId : FieldId
  }
  trait IRSetField extends IRExpr {
    def fieldId : FieldId
    def newValue : IRExpr
  }



  trait IRCallQuery extends IRMethodCall {
    def recv : IRExpr
    def methodId : MethodId
    def arguments : Seq[IRExpr]
  }
  trait IRCallUpdateThis extends IRMethodCall {
    def methodId : MethodId
    def arguments : Seq[IRExpr]
  }
  trait IRCallUpdateField extends IRMethodCall {
    def fieldId : FieldId
    def methodId : MethodId
    def arguments : Seq[IRExpr]
  }

  object BaseExpressions {
    case class NumExpr(value : Int) extends IRNum
    case object TrueExpr extends IRTrue
    case object FalseExpr extends IRFalse
    case class StringExpr(value : String) extends IRString
    case object UnitExpr extends IRUnit

    case class VarExpr(id : VarId) extends IRVar
    case class LetExpr(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRLet
    case class IfExpr(conditionExpr : IRExpr, thenExpr : IRExpr, elseExpr : IRExpr) extends IRIf
    case class EqualsExpr(expr1 : IRExpr, expr2 : IRExpr) extends IREquals
    case object ThisExpr extends IRThis
    case class GetFieldExpr(fieldId : FieldId) extends IRGetField
    case class SetFieldExpr(fieldId : FieldId, newValue : IRExpr) extends IRSetField

    case class CallQueryExpr(recv : IRExpr, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallQuery
    case class CallUpdateThisExpr(methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateThis
    case class CallUpdateFieldExpr(fieldId : FieldId, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateField
  }

  object TypedExpressions {
    case class NumTExpr(value : Int, typ : Type) extends IRNum with TypedExpr
    case object TrueExpr extends IRTrue with TypedExpr
    case object FalseExpr extends IRFalse with TypedExpr
    case class StringExpr(value : String) extends IRString with TypedExpr
    case object UnitExpr extends IRUnit with TypedExpr

    case class VarExpr(id : VarId) extends IRVar with TypedExpr
    case class LetExpr(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRLet with TypedExpr
    case class IfExpr(conditionExpr : IRExpr, thenExpr : IRExpr, elseExpr : IRExpr) extends IRIf with TypedExpr
    case class EqualsTExpr(expr1 : TypedExpr, expr2 : IRExpr, typ : Type) extends IREquals with TypedExpr

    case object ThisExpr extends IRThis with TypedExpr
    case class GetFieldExpr(fieldId : FieldId) extends IRGetField with TypedExpr
    case class SetFieldExpr(fieldId : FieldId, newValue : IRExpr) extends IRSetField with TypedExpr
    case class CallQueryExpr(recv : IRExpr, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallQuery with TypedExpr
    case class CallUpdateThisExpr(methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateThis with TypedExpr
    case class CallUpdateFieldExpr(fieldId : FieldId, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateField with TypedExpr
  }


}
