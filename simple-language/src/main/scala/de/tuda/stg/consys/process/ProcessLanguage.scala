package de.tuda.stg.consys.process

/**
	* Created on 24.07.19.
	*
	* @author Mirko Köhler
	*/
trait ProcessLanguage {

	type Loc
	type Lab
	type Method
	type Var

	type Cls
	type Fld

	trait Expression
	trait Value extends Expression
	case class Location(loc : Loc, lab : Lab) extends Expression with Value
	case class V(x : Var) extends Expression
	case class Operation(e : Expression, m : Method, arg : Expression) extends Expression
	case class Let(x : Var, e : Expression, body : Expression) extends Expression
	case class New(cls : Cls, lab : Lab, fields : Map[Fld, Expression]) extends Expression

	def isValue(e : Expression) : Boolean = e.isInstanceOf[Value]

}
