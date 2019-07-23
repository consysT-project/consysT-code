package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Condition

object Condition {
	case class Bool(b : Boolean) extends Condition
	case class InstanceOf(expr : Expression, className : ClassName) extends Condition
	case class HasLabel(addr : Addr, label : Label) extends Condition
	case class And(c1 : Condition, c2 : Condition) extends Condition
	case class Not(c1 : Condition) extends Condition

}
