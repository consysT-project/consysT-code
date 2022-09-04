package de.tuda.stg.consys.invariants.lang


sealed trait Expr

object Expr {

	sealed trait Val extends Expr
	sealed trait Op extends Expr


	case object UnitVal extends Val
	case class BoolVal(v : Boolean) extends Val
	case class IntVal(i : Int) extends Val
	case class SetVal(xs : Set[Val]) extends Val
	case class PairVal(x1 : Val, x2 : Val) extends Val
	case class RefVal(ref : RefId) extends Val

	case class Var(x : VarId) extends Expr
	case class LetExpr(x : VarId, t : Type, e : Expr, body : Expr) extends Expr
	case class MakePairExpr(e1 : Expr, e2 : Expr) extends Expr

	case class PlusOp(e1 : Expr, e2 : Expr) extends Op
	case class FstOp(e : Expr) extends Op
	case class SndOp(e : Expr) extends Op


	def interp(env : VarEnv, expr : Expr) : Val = {
		expr match {
			case v : Val => v

			case Var(x) => env(x)

			case LetExpr(x, t, e, body) =>
				val v1 = interp(env, e)
				interp(env + (x -> v1), body)


			case MakePairExpr(e1, e2) =>
				val v1 = interp(env, e1)
				val v2 = interp(env, e2)
				PairVal(v1, v2)


			case PlusOp(e1, e2) =>
				val IntVal(i1) = interp(env, e1)
				val IntVal(i2) = interp(env, e2)
				IntVal(i1 + i2)

			case FstOp(e) =>
				val PairVal(v1, v2) = interp(env, e)
				v1

			case SndOp(e) =>
				val PairVal(v1, v2) = interp(env, e)
				v2
		}
	}





}


