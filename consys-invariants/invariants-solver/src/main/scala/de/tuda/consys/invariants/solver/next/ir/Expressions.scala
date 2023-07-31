package de.tuda.consys.invariants.solver.next.ir

import de.tuda.consys.invariants.solver.next.ir.Expressions.BaseExpressions
import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassId, FieldId, MethodId, VarId}
import de.tuda.consys.invariants.solver.next.ir.Types.Type

object Expressions {

  trait BaseExpressions {
    type Expr <: BaseExpr

    trait BaseExpr
    trait BaseUnit extends BaseExpr
    trait BaseVar extends BaseExpr {
      def id : VarId
    }
    trait BaseLet extends BaseExpr {
      def id : VarId
      def namedExpr : Expr
      def bodyExpr : Expr
    }
    trait BaseIf extends BaseExpr {
      def conditionExpr : Expr
      def thenExpr : Expr
      def elseExpr : Expr
    }
    trait BaseEquals extends BaseExpr {
      def expr1 : Expr
      def expr2 : Expr
    }
  }

  trait BaseNumExpressions extends BaseExpressions {
    trait BaseNum extends BaseExpr {
      def value : Int
    }
  }

  trait BaseBoolExpressions extends BaseExpressions {
    trait BaseTrue extends BaseExpr
    trait BaseFalse extends BaseExpr
  }

  trait BaseStringExpressions extends BaseExpressions {
    trait BaseString extends BaseExpr {
      def value : String
    }
  }

  trait BaseObjectExpressions extends BaseExpressions {
    trait BaseThis extends BaseExpr

    trait BaseNew extends BaseExpr {
      def classId : ClassId
      def typeArguments : Seq[Type]
      def arguments : Map[FieldId, Expr]
    }

    trait BaseGetField extends BaseExpr {
      def fieldId : FieldId
    }

    trait BaseSetField extends BaseExpr {
      def fieldId : FieldId
      def newValue : Expr
    }

    trait BaseCallQuery extends BaseExpr {
      def recv : Expr
      def methodId : MethodId
      def arguments : Seq[Expr]
    }

    trait BaseCallUpdateThis extends BaseExpr {
      def methodId : MethodId
      def arguments : Seq[Expr]
    }

    trait BaseCallUpdateField extends BaseExpr {
      def fieldId : FieldId
      def methodId : MethodId
      def arguments : Seq[Expr]
    }
  }

  trait UntypedExpressions extends BaseExpressions {
    type Expr <: UntypedExpr

    trait UntypedExpr extends BaseExpr

    case object IRUnit extends UntypedExpr with BaseUnit
    case class IRVar(override val id : VarId) extends UntypedExpr with BaseVar
    case class IRLet(override val id : VarId, override val namedExpr : Expr, override val bodyExpr : Expr) extends UntypedExpr with  BaseLet
    case class IRIf(override val conditionExpr : Expr, override val thenExpr : Expr, override val elseExpr : Expr) extends UntypedExpr with  BaseIf
    case class IREquals(override val expr1 : Expr, override val expr2 : Expr) extends UntypedExpr with  BaseEquals
  }

  trait UntypedNumExpressions extends UntypedExpressions with BaseNumExpressions {
    case class IRNum(override val value : Int) extends UntypedExpr with BaseNum
  }

  trait UntypedBoolExpressions extends UntypedExpressions with BaseBoolExpressions {
    case object IRTrue extends UntypedExpr with BaseTrue
    case object IRFalse extends UntypedExpr with BaseFalse
  }


  trait UntypedStringExpressions extends UntypedExpressions with BaseStringExpressions {
    case class IRString(override val value : String) extends UntypedExpr with BaseString
  }

  trait UntypedObjectExpressions extends UntypedExpressions with BaseObjectExpressions {

    case object IRThis extends UntypedExpr with BaseThis

    case class IRNew(override val classId: ClassId, override val typeArguments : Seq[Type], override val arguments : Map[FieldId, Expr]) extends UntypedExpr with BaseNew

    case class IRGetField(override val fieldId : FieldId) extends UntypedExpr with BaseGetField
    case class IRSetField(override val fieldId : FieldId, override val newValue : Expr) extends UntypedExpr with BaseSetField
    case class IRCallQuery(override val recv : Expr, override val methodId : MethodId, override val arguments : Seq[Expr]) extends UntypedExpr with BaseCallQuery
    case class IRCallUpdateThis(override val methodId : MethodId, override val arguments : Seq[Expr]) extends UntypedExpr with BaseCallUpdateThis
    case class IRCallUpdateField(override val fieldId : FieldId, override val methodId : MethodId, override val arguments : Seq[Expr]) extends UntypedExpr with BaseCallUpdateField
  }




  trait TypedExpressions extends BaseExpressions {
    type Expr <: TypedExpr

    trait TypedExpr extends BaseExpr {
      def typ : Type
    }

    case class IRUnit(override val typ : Type) extends TypedExpr with BaseUnit
    case class IRVar(override val id : VarId, override val typ : Type) extends TypedExpr with BaseVar
    case class IRLet(override val id : VarId, override val namedExpr : Expr, override val bodyExpr : Expr, override val typ : Type) extends TypedExpr with BaseLet
    case class IRIf(override val conditionExpr : Expr, override val thenExpr : Expr, override val elseExpr : Expr, override val typ : Type) extends TypedExpr with BaseIf
    case class IREquals(override val expr1 : Expr, override val expr2 : Expr, override val typ : Type) extends TypedExpr with BaseEquals
  }

  trait TypedNumExpressions extends TypedExpressions with BaseNumExpressions {
    case class IRNum(override val value : Int, override val typ : Type) extends TypedExpr with BaseNum
  }

  trait TypedBoolExpressions extends TypedExpressions with BaseBoolExpressions {
    case class IRTrue(override val typ : Type) extends TypedExpr with BaseTrue
    case class IRFalse(override val typ : Type) extends TypedExpr with BaseFalse
  }

  trait TypedStringExpressions extends TypedExpressions with BaseStringExpressions {
    case class IRString(override val value : String, override val typ : Type) extends TypedExpr with BaseString
  }

  trait TypedObjectExpressions extends TypedExpressions with BaseObjectExpressions {
    case class IRThis(override val typ : Type) extends TypedExpr with BaseThis

    case class IRNew(override val classId: ClassId, override val typeArguments : Seq[Type], override val arguments : Map[FieldId, Expr], override val typ : Type) extends TypedExpr with BaseNew

    case class IRGetField(override val fieldId : FieldId, override val typ : Type) extends TypedExpr with BaseGetField
    case class IRSetField(override val fieldId : FieldId, override val newValue : Expr, override val typ : Type) extends TypedExpr with BaseSetField
    case class IRCallQuery(override val recv : Expr, override val methodId : MethodId, override val arguments : Seq[Expr], override val typ : Type) extends TypedExpr with BaseCallQuery
    case class IRCallUpdateThis(override val methodId : MethodId, override val arguments : Seq[Expr], override val typ : Type) extends TypedExpr with BaseCallUpdateThis
    case class IRCallUpdateField(override val fieldId : FieldId, override val methodId : MethodId, override val arguments : Seq[Expr], override val typ : Type) extends TypedExpr with BaseCallUpdateField
  }


  trait BaseLang {
    self : BaseExpressions
      with BaseNumExpressions
      with BaseBoolExpressions
      with BaseStringExpressions
      with BaseObjectExpressions =>
  }

  object UntypedLang extends BaseLang
    with UntypedExpressions
    with UntypedNumExpressions
    with UntypedBoolExpressions
    with UntypedStringExpressions
    with UntypedObjectExpressions {

    override type Expr = UntypedExpr
  }

  object TypedLang extends BaseLang
    with TypedExpressions
    with TypedNumExpressions
    with TypedBoolExpressions
    with TypedStringExpressions
    with TypedObjectExpressions {

    override type Expr = TypedExpr
  }

//  sealed trait IRExpr
//  sealed trait IRLiteral extends IRExpr
//
//  sealed trait IRMethodCall extends IRExpr {
//    def arguments : Seq[IRExpr]
//    def methodId : MethodId
//  }
//
//  trait TypedExpr {
//    def typ : Type
//  }
//

//
//  object BaseExpressions {
//    case class NumExpr(value : Int) extends IRNum
//    case object TrueExpr extends IRTrue
//    case object FalseExpr extends IRFalse
//    case class StringExpr(value : String) extends IRString
//    case object UnitExpr extends IRUnit
//
//    case class VarExpr(id : VarId) extends IRVar
//    case class LetExpr(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRLet
//    case class IfExpr(conditionExpr : IRExpr, thenExpr : IRExpr, elseExpr : IRExpr) extends IRIf
//    case class EqualsExpr(expr1 : IRExpr, expr2 : IRExpr) extends IREquals
//    case object ThisExpr extends IRThis
//    case class GetFieldExpr(fieldId : FieldId) extends IRGetField
//    case class SetFieldExpr(fieldId : FieldId, newValue : IRExpr) extends IRSetField
//
//    case class CallQueryExpr(recv : IRExpr, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallQuery
//    case class CallUpdateThisExpr(methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateThis
//    case class CallUpdateFieldExpr(fieldId : FieldId, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateField
//  }

//  object TypedExpressions {
//    case class NumTExpr(value : Int, typ : Type) extends IRNum with TypedExpr
//    case object TrueExpr extends IRTrue with TypedExpr
//    case object FalseExpr extends IRFalse with TypedExpr
//    case class StringExpr(value : String) extends IRString with TypedExpr
//    case object UnitExpr extends IRUnit with TypedExpr
//
//    case class VarExpr(id : VarId) extends IRVar with TypedExpr
//    case class LetExpr(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRLet with TypedExpr
//    case class IfExpr(conditionExpr : IRExpr, thenExpr : IRExpr, elseExpr : IRExpr) extends IRIf with TypedExpr
//    case class EqualsTExpr(expr1 : TypedExpr, expr2 : IRExpr, typ : Type) extends IREquals with TypedExpr
//
//    case object ThisExpr extends IRThis with TypedExpr
//    case class GetFieldExpr(fieldId : FieldId) extends IRGetField with TypedExpr
//    case class SetFieldExpr(fieldId : FieldId, newValue : IRExpr) extends IRSetField with TypedExpr
//    case class CallQueryExpr(recv : IRExpr, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallQuery with TypedExpr
//    case class CallUpdateThisExpr(methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateThis with TypedExpr
//    case class CallUpdateFieldExpr(fieldId : FieldId, methodId : MethodId, arguments : Seq[IRExpr]) extends IRCallUpdateField with TypedExpr
//  }


}
