package de.tuda.stg.consys.process

/**
	* Created on 24.07.19.
	*
	* @author Mirko Köhler
	*/
trait ExtendedProcessLanguage extends ProcessLanguage {

	case class Num(n : Int) extends Expression with Value
	case class Add(e1 : Expression, e2 : Expression) extends Expression
	case class Mul(e1 : Expression, e2 : Expression) extends Expression

}
