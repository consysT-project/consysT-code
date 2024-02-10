package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{Sort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Type}
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Type._

class Translator(val context : Z3Context) {

	def translateType(typ : Type) : Sort = typ match {
		case TBool => context.getBoolSort
		case TInt => context.getIntSort
		case TUnit => context.getIntSort
		case TRef(c) => ???
		case TPair(t1, t2) => ???
		case TSet(t) => context.mkSetSort(translateType(t))
	}

	def translateExpression(expr : Expression) : Z3Expr[_] = expr match {
		case VUnit => context.mkInt(0)
		case VBool(b) => context.mkBool(b)
		case VInt(i) => context.mkInt(i)
		case VSet(typ, xs) => ???
		case VPair(x1, x2) => ???
		case VRef(c, ref) => ???
		case VString(s) => context.mkString(s)

		case EVar(x) => ???
	}

}
