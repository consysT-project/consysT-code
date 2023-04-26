package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{Context, Sort, Expr => Z3Expr}
import de.tuda.consys.invariants.solver.next.ir.IR._
import de.tuda.consys.invariants.solver.next.translate.TypeRep.ObjectTypeRep
trait ExpressionParser {

	def parse(expr : IRExpr, vars : Map[VarId, Z3Expr[_]]) : Z3Expr[_] = {
		throw ParseException("unknown expression: " + expr)
	}

}

object ExpressionParser {

	class BaseExpressionParser(ctx : Context) extends ExpressionParser {

		override def parse(expr : IRExpr, vars : Map[VarId, Z3Expr[_]]) : Z3Expr[_] = expr match {
			case Num(n) => ctx.mkInt(n)

			case Var(x) => vars.getOrElse(x, throw ParseException("variable not found: " + x))

			case Equals(e1, e2) =>
				val expr1 : Z3Expr[Sort] = parse(e1, vars).asInstanceOf[Z3Expr[Sort]]
				val expr2 : Z3Expr[Sort] = parse(e2, vars).asInstanceOf[Z3Expr[Sort]]
				ctx.mkEq(expr1, expr2)

			case Let(id, namedExpr, body) =>
				val named = parse(namedExpr, vars)
				parse(body, vars + (id -> named))

			case _ => super.parse(expr, vars)
		}
	}

	class ObjectClassExpressionParser(ctx : Context, thisExpr : Z3Expr[_], cls : ObjectTypeRep) extends BaseExpressionParser(ctx) {
		override def parse(expr : IRExpr, vars : Map[VarId, Z3Expr[_]]) : Z3Expr[_] = expr match {
			case GetField(id) =>
				val fieldAcc = cls.accessors.getOrElse(id, throw ParseException(s"field not found: $id (in class $cls)"))
				ctx.mkApp(fieldAcc, thisExpr)

			case This =>
				thisExpr

			case _ => super.parse(expr, vars)
		}
	}

	class MethodBodyExpressionParser(ctx : Context, thisExpr : Z3Expr[_], cls : ObjectTypeRep)

}
