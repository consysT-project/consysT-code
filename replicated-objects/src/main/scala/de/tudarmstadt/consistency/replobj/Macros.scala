package de.tudarmstadt.consistency.replobj

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
object Macros {

	def m(arg : Int) : String = macro mImpl

	def mImpl(c : whitebox.Context)(arg : c.Expr[Int]) : c.Expr[String] = {
		import c.universe._
		val s = arg.tree.toString()

		c.Expr[String](Literal(Constant(s)))
	}

}

