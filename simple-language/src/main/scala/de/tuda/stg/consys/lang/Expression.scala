package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Expression

object Expression {
	case class Var(name : VarName) extends Expression
	//For now: only consider accessing fields of THIS object.
	case class Field(name : FieldName) extends Expression
	case object This extends Expression
	case class Call(receiver : Expression, method : MethodName, arguments : Seq[Expression]) extends Expression
	case class New(typ : Type, arguments : Seq[Expression]) extends Expression
}