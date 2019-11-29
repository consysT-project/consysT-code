package de.tuda.stg.consys.experimental.lang

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
trait IntSemantics extends LocalSemantics { self : IntSyntax =>

	override def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
		case Add(Num(n1), Num(n2)) => Num(n1 + n2)
		case Add(expr1 : Num, expr2) => Add(expr1, reduceExpr(vars, expr2))
		case Add(expr1, expr2) => Add(reduceExpr(vars, expr1), expr2)

		case _ => super.reduceExpr(vars, expr)
	}

}
