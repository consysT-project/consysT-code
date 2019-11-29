package de.tuda.stg.consys.experimental.lang

import scala.language.implicitConversions

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait IntSyntax extends Syntax {

	/* Expressions */
	case class Num(n : Int) extends Value {
		override def prettyString : String = s"$n"
	}
	case class Add(expr1 : Expression, expr2 : Expression) extends Expression {
		override def prettyString : String = s"($expr1 + $expr2)"
	}


}

