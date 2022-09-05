package de.tuda.stg.consys.invariants.lang


sealed trait Expr

object Expr {

	sealed trait Val extends Expr
	sealed trait Op extends Expr

	case object UnitVal extends Val
	case class BoolVal(v : Boolean) extends Val
	case class IntVal(i : Int) extends Val
	case class SetVal(t : Type, xs : Set[Val]) extends Val
	case class PairVal(x1 : Val, x2 : Val) extends Val
	case class RefVal(c : ClassId, ref : RefId) extends Val
	case class StringVal(s : String) extends Val

	case class Var(x : VarId) extends Expr
	case class LetExpr(x : VarId, e : Expr, body : Expr) extends Expr
	case class PairExpr(e1 : Expr, e2 : Expr) extends Expr

	case class PlusOp(e1 : Expr, e2 : Expr) extends Op
	case class FstOp(e : Expr) extends Op
	case class SndOp(e : Expr) extends Op









}


