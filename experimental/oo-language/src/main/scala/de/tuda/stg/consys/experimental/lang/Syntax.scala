package de.tuda.stg.consys.experimental.lang

import scala.language.implicitConversions

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait Syntax {

	type VarId
	type FieldId
	type MethodId
	type Location

	trait Pretty {
		def prettyString : String = super.toString
		override def toString : String = prettyString
	}

	trait Expression extends Pretty
	trait Value extends Expression
	case class Var(x : VarId) extends Expression {
		override def prettyString : String = s"$x"
	}


	trait Statement extends Pretty
	case class Return(expr : Expression) extends Statement {
		override def prettyString : String = s"RETURN $expr"
	}
	case class Bind(expr : Expression, cc : Continuation) extends Statement {
		override def prettyString : String = s"BIND ${cc.x} := $expr IN ${cc.next}"
	}

	/* Continuations */
	case class Continuation(x : VarId, next : Statement)

	/* Defines a method */
	case class MethodDef(x : VarId, body : Statement)

	/*

DO ('n := NEW("O", Map(), Map())) IN
DO 'x := NEW("Hello", Map("f" -> Loc("O"), Map()) IN



 */
}

