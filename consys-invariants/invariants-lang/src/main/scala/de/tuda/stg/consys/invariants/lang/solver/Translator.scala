package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, Sort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.TypeSystem
import de.tuda.stg.consys.invariants.lang.TypeSystem.TypeMap
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Type}
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Type._

class Translator(val context : Z3Context) {

	private case class TranslationError(msg : String) extends Exception(msg)

	private def error(msg : String) : Nothing =
		throw TranslationError(msg)

	def translateType(typ : Type) : Sort = typ match {
		case TBool => context.getBoolSort
		case TInt => context.getIntSort
		case TUnit => context.getIntSort
		case TRef(c) => ???
		case TPair(t1, t2) => ???
		case TSet(t) => context.mkSetSort(translateType(t))
	}

	def translateExpression(typeMap : TypeMap, expr : Expression) : Z3Expr[_] = expr match {
		case VUnit => context.mkInt(0)
		case VBool(b) => context.mkBool(b)
		case VInt(i) => context.mkInt(i)
		case VSet(typ, xs) => ???
		case VPair(x1, x2) => ???
		case VRef(c, ref) => ???
		case VString(s) => context.mkString(s)

		case EVar(x) =>
			val typ = typeMap.getOrElse(expr.nodeId, error(s"type for $expr cannot be resolved"))
			val sort = translateType(typ)
			context.mkConst(x, sort)

		case EPlus(e1, e2) =>
			val z1 = translateExpression(typeMap, e1).asInstanceOf[Z3Expr[ArithSort]]
			val z2 = translateExpression(typeMap, e2).asInstanceOf[Z3Expr[ArithSort]]
			context.mkAdd(z1, z2)
	}

}

object Translator {
	def main(args : Array[String]) : Unit = {

		val expr = EPlus(VInt(42), VInt(23))()
		val typeResult = TypeSystem.checkExpr(Map(), expr)

		val z3Ctx = new Z3Context()
		val trans = new Translator(z3Ctx)

		val z3Expr = trans.translateExpression(typeResult.typeMap, expr)
		println(z3Expr)

	}
}
