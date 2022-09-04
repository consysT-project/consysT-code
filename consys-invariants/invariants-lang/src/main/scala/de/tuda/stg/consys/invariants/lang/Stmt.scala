package de.tuda.stg.consys.invariants.lang

sealed trait Stmt

object Stmt {

	case class Return(e : Expr) extends Stmt
	case class DoNew(x : VarId, c : ClassId, fields : Map[FieldId, Expr], body : Stmt) extends Stmt
	case class DoGetField(x : VarId, f : FieldId, body : Stmt) extends Stmt
	case class DoSetField(x : VarId, f : FieldId, e : Expr, body : Stmt) extends Stmt
	case class DoCallMethod(x : VarId, recv : Expr, m : MethodId, args : Seq[Expr], body : Stmt) extends Stmt

}
