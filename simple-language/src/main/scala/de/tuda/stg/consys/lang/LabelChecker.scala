package de.tuda.stg.consys.lang

import de.tuda.stg.consys.lang.Computation.{Assignment, Skip}
import de.tuda.stg.consys.lang.Label.{ConcreteLabel, ConsistencyLabel, LOCAL}

/**
	* Created on 08.07.19.
	*
	* @author Mirko Köhler
	*/
trait LabelChecker {

	class LabelError(msg : String = "type error") extends Exception(msg)

	type Env = Map[VarName, ConcreteLabel]

	def checkComputation(env : Env, pc : ConcreteLabel, c : Computation) : Unit = c match {
		case Skip =>
		case Assignment(x, e) =>


//			(pc, env(x), checkExpression(env, e)) match {
//				case (LOCAL, _) =>
//				case (_, LOCAL) =>
//				case (c1 : ConsistencyLabel, c2 : ConsistencyLabel) => c1 isSmallerEq
//			}
	}

	def checkExpression(env : Env, e : Expression) : ConcreteLabel = e match {
		case _ => ???
	}


}
