package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Computation

object Computation {
	case object Skip extends Computation

	case class Store(addr : Addr, expr : Expression) extends Computation
	case class Invoke(x : VarName, addr : Addr, method : MethodName, arg : Expression) extends Computation
	case class Assign(x : VarName, expr : Expression) extends Computation

	case class Sequence(c1 : Computation, c2 : Computation) extends Computation
	case class Ifte(cond : Condition, thenBranch : Computation, elseBranch : Computation) extends Computation
	case class While(cond : Condition, body : Computation) extends Computation
}
