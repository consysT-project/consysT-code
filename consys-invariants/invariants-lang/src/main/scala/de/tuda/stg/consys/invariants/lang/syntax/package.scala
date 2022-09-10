package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.ClassDef.{FieldDef, MethodDef, VarDef}
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement.{DoCallMethod, DoExpr, DoNew, DoSetField}
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement, Type}

import scala.language.implicitConversions

package object syntax {

  /* Syntax for Expressions */
  def Plus(e1 : Expression, e2 : Expression) : Expression =
    EPlus(e1, e2)()

  def Fst(e : Expression) : Expression =
    EFst(e)()

  def Snd(e : Expression) : Expression =
    ESnd(e)()

  def Var(x : String) : Expression =
    EVar(x)()

  def Fld(f : FieldId) : Expression =
    EField(f)()

  def Num(i : Int) : Val =
    VInt(i)

  def Text(s : String) : Val =
    VString(s)

  implicit class ExpressionOps(e1 : Expression) {
    def +(e2 : Expression) : Expression = EPlus(e1, e2)()
  }

  case class Let(varDef : ExpressionVariableDefinition*) {
    def in(body : Expression) : Expression = {
      varDef.foldRight(body)((vDef, expr) =>
        ELet(vDef.x, vDef.namedExpr, expr)()
      )
    }
  }

  implicit class ExpressionVariableDeclaration(x : VarId) {
    def :=(namedExpr : Expression) : ExpressionVariableDefinition =
      ExpressionVariableDefinition(x, namedExpr)
  }

  case class ExpressionVariableDefinition private[syntax](x : VarId, namedExpr : Expression)


  /* Syntax for Statements */

  def Return(expression: Expression) : Statement =
    Statement.Return(expression)()

  case class Do(varDef : StatementVariableDefinition) {
    def in(body : Statement) : Statement = varDef.frag match {
      case DoNewVariableDeclartionFragment(cls, fields) => DoNew(varDef.x, cls, fields, body)()
      case DoExpressionDeclarationFragment(expr) => DoExpr(varDef.x, expr, body)()
      case DoSetFieldVariableDeclartionFragment(field, newExpr) => DoSetField(varDef.x, field, newExpr, body)()
      case DoCallMethodVariableDeclartionFragment(receiver, m, args) => DoCallMethod(varDef.x, receiver, m, args, body)()
    }
  }

  implicit class StatementVariableDeclaration(x : VarId) {
    def <<(fragment : StatementVariableDeclarationFragment) : StatementVariableDefinition =
      StatementVariableDefinition(x, fragment)

    def <<(expr : Expression) : StatementVariableDefinition =
      StatementVariableDefinition(x, DoExpressionDeclarationFragment(expr))

  }

  def New(cls : ClassId, fields : Expression*) : StatementVariableDeclarationFragment =
    DoNewVariableDeclartionFragment(cls, fields)

  def Set(field : FieldId, newExpr : Expression) : StatementVariableDeclarationFragment =
    DoSetFieldVariableDeclartionFragment(field, newExpr)

  def Call(receiver : Expression, m : MethodId)(args : Expression*) : StatementVariableDeclarationFragment =
    DoCallMethodVariableDeclartionFragment(receiver, m, args)



  sealed trait StatementVariableDeclarationFragment
  private case class DoNewVariableDeclartionFragment(cls : ClassId, fields : Seq[Expression]) extends StatementVariableDeclarationFragment
  private case class DoExpressionDeclarationFragment(expr : Expression) extends StatementVariableDeclarationFragment
  private case class DoSetFieldVariableDeclartionFragment(field : FieldId, newExpr : Expression) extends StatementVariableDeclarationFragment
  private case class DoCallMethodVariableDeclartionFragment(receiver : Expression, m : MethodId, args : Seq[Expression]) extends StatementVariableDeclarationFragment

  case class StatementVariableDefinition private[syntax](x : VarId, frag : StatementVariableDeclarationFragment)



  /* Syntax for class definitions */
  case class Class(clsId : ClassId) {
    def as(classFragments : ClassFragment*) : ClassDef = {
      val (fieldDefs, methodDefs) = classFragments.foldLeft((Seq.empty[FieldDef], Seq.empty[MethodDef])) {
        (seqs, frag) =>
          frag match {
            case ClassFieldFragment(f, typ) => (seqs._1 :+ FieldDef(typ, f), seqs._2)
            case ClassMethodFragment(m, typ, parameters, body) => (seqs._1, seqs._2 :+ MethodDef(typ, m, parameters, body))
          }
      }

      ClassDef(clsId, fieldDefs, methodDefs)
    }
  }

  case object Define {
    case class Class(clsId : ClassId) {
      def as(classFragments : ClassFragment*) : ClassDef = {
        val cls = syntax.Class(clsId).as(classFragments : _*)
        ClassTable.define(cls)
        cls
      }
    }
  }

  def field(varDecl : TypedDeclaration) : ClassFragment = ClassFieldFragment(varDecl.x, varDecl.typ)
  def method(methodName : TypedDeclaration)(args : TypedDeclaration*)(body : Statement) : ClassFragment = ClassMethodFragment(methodName.x, methodName.typ, args.map(decl => VarDef(decl.typ, decl.x)), body)


  case class TypedDeclaration(x : String, typ : Type)

  implicit class TypeOps(t : Type) {
    def ::(x : String) : TypedDeclaration = TypedDeclaration(x, t)
  }

  sealed trait ClassFragment
  private case class ClassFieldFragment(f : FieldId, typ : Type) extends ClassFragment
  private case class ClassMethodFragment(m : MethodId, typ : Type, parameters : Seq[VarDef], body : Statement) extends ClassFragment




  /* Implicit conversions */
  implicit def unitToVal(u : Unit) : Val = VUnit

  implicit def boolToVal(b : Boolean) : Val = VBool(b)

  implicit def intToVal(i : Int) : Val = VInt(i)

  implicit def varToExpr(x : String) : Expression = EVar(x)()

  implicit def pairToExpr(p : (Expression, Expression)) : Expression = EPair(p._1, p._2)()


}
