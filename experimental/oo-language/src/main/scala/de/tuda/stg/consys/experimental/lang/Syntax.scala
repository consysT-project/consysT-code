package de.tuda.stg.consys.experimental.lang

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

	trait Value extends Expression
	trait Expression
	case object Nix extends Value
	case class Loc(addr : Location) extends Value
	case class Var(x : VarId) extends Expression
//	case class New(fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef]) extends Expression
//	case class FieldGet(fld : FieldId) extends Expression

	trait CCStatement
	case class CCReturn(expr : Expression) extends CCStatement
	case class CCNew(loc : Location, fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef], cc : Continuation) extends CCStatement
	case class CCFieldSet(objExpr : Expression, field : FieldId, expr : Expression, cc : Continuation) extends CCStatement
	case class CCFieldGet(objExpr : Expression, field : FieldId, cc : Continuation) extends CCStatement
	case class CCInvoke(objExpr : Expression, method : MethodId, param : Expression, cc : Continuation) extends CCStatement

	/* Object store */
	type ObjectStore = Map[Location, Obj]

	/* Stored in the store */
	case class Obj(fields : Map[FieldId, Value], methods : Map[MethodId, MethodDef])

	/* Defines a method */
	case class MethodDef(x : VarId, body : CCStatement)

	/* Continuations */
	case class Continuation(x : VarId, next : CCStatement)

}

