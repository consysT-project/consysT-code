package de.tuda.stg.consys.process

import de.tuda.stg.consys.process.SimpleInterpreter.{Label, Weak}

/**
	* Created on 24.07.19.
	*
	* @author Mirko Köhler
	*/
class SimpleInterpreter(replicaId : Int)
	extends ExtendedProcessLanguage
	with SimpleProcessReduction {

	override type Loc = (Int, Int)
	override type Lab = Label
	override type Method = Symbol
	override type Var = Symbol
	override type Fld = Symbol

	private var currentLoc = 0
	override def newloc : Loc = {
		currentLoc += 1
		(replicaId, currentLoc)
	}

	override def isAsync(lab : Lab) : Boolean =
		lab == Weak


	val clsCounter : Cls = FunCls(
		fields = Set('value),
		methods = Map('inc -> ((ths, v) => {
			val Num(currentValue) = ths.fields('value)
			(
				Obj(ths.cls, ths.lab, Map('value -> Num(currentValue + 1))),
				Num(currentValue)
			)
		}))
	)

}

object SimpleInterpreter {


	sealed trait Label
	case object Strong extends Label
	case object Weak extends Label





	def main(args : Array[String]) : Unit = {
		val interp = new SimpleInterpreter(0)

		import interp._

		val expr = Let('counter, New(clsCounter, Weak, Map('value -> Num(0))),
			Operation(V('counter), 'inc, Num(0))
		)

		val ret =interp.reduceAll(expr, Map())

		println(s"return = $ret")

	}

}
