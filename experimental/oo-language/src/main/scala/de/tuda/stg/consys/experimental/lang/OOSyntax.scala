package de.tuda.stg.consys.experimental.lang

import scala.language.implicitConversions

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait OOSyntax extends Syntax {


	/* Expressions */
	case object Nix extends Value
	case class Loc(addr : Location) extends Value {
		override def prettyString : String = s"$$$addr"
	}

//	case class New(fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef]) extends Expression
//	case class FieldGet(fld : FieldId) extends Expression

	/* Statements */
	case class New(loc : Location, fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef], cc : Continuation) extends Statement {
		override def prettyString : String = s"DO ${cc.x} := NEW($loc, $fields, $methods) IN\n${cc.next}"
	}
	case class FieldSet(objExpr : Expression, field : FieldId, expr : Expression, cc : Continuation) extends Statement {
		override def prettyString : String = s"DO ${cc.x} := $objExpr.$field <- $expr IN\n${cc.next}"
	}
	case class FieldGet(objExpr : Expression, field : FieldId, cc : Continuation) extends Statement {
		override def prettyString : String = s"DO ${cc.x} := $objExpr.$field IN\n${cc.next}"
	}
	case class Invoke(objExpr : Expression, method : MethodId, param : Expression, cc : Continuation) extends Statement {
		override def prettyString : String = s"DO ${cc.x} := $objExpr.$method($param) IN\n${cc.next}"
	}





}

