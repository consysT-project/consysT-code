package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Expression

object Expression {
	case class Var(name : VarName) extends Expression
	case class Field(fieldName: FieldName) extends Expression
	case class New(cls : ClassName, fields : Seq[Expression]) extends Expression
}