package de.tuda.stg.consys.lang

import de.tuda.stg.consys.lang.Computation.{Assign, Ifte, Invoke, Sequence, Skip, Store}
import de.tuda.stg.consys.lang.Condition.{Bool, HasLabel, InstanceOf}
import de.tuda.stg.consys.lang.Expression.{Field, New, Var}
import de.tuda.stg.consys.lang.Label.ConsistencyLabel

/**
	* Created on 11.07.19.
	*
	* @author Mirko Köhler
	*/
trait OperationalSemantics {


	def isValue(expr : Expression) : Boolean = expr match {
		case New(cls, flds) if flds.forall(isValue) => true
		case _ => false
	}

	def classTable : ClassTable

	type LocEnv = Map[VarName, Expression]
	type Replica = Map[Addr, (ConsistencyLabel, Expression)]

	type ClassTable = Map[ClassName, CDef]


	case class Configuration(env : LocEnv, rep : Replica) {
		def store(addr : Addr, expr : Expression) : Configuration = {
			require(isValue(expr))
			copy(rep = rep + (addr -> expr))
		}

		def assign(x : VarName, expr : Expression) : Configuration = {
			require(isValue(expr))
			copy(env = env + (x -> expr))
		}
	}

	def cStep(conf : Configuration, c : Computation) : (Configuration, Computation) = c match {
		case Skip =>
			(conf, c)

		case Store(addr, expr@New(cls, flds)) if isValue(expr) =>
			(conf.store(addr, expr), Skip)

		case Store(addr, expr) =>
			(conf, Store(addr, eStep(conf, expr)))

		case Invoke(x, addr, method, arg) if isValue(arg) =>
			//Start transaction
			???

		case Invoke(x, addr, method, arg) =>
			(conf, Invoke(x, addr, method, eStep(conf, arg)))


		case Assign(x, expr) if isValue(expr) =>
			(conf.assign(x, expr), Skip)

		case Assign(x, expr) =>
			(conf, Assign(x, eStep(conf, expr)))


		case Sequence(Skip, c2) =>
			(conf, c2)

		case Sequence(c1, c2) =>
			val (cconf, cc) = cStep(conf, c1)
			(cconf, Sequence(cc, c2))


		case Ifte()
	}


	def eStep(conf : Configuration, e : Expression) : Expression = e match {
		case Var(x) => conf.env(x)

		case Field(f) =>
			val New(cls, fields) = conf.env('this)
			val fieldIdx = classTable(cls).fields.indexWhere(fdef => fdef.name == f)
			fields(fieldIdx)

		case New(cls, fields) =>
			val fIdx = fields.indexWhere(expr => !isValue(expr))
			if (fIdx == -1) return e
			val newFields = fields.take(fIdx) ++ Seq(eStep(conf, fields(fIdx))) ++ fields.drop(fIdx + 1)
			New(cls, newFields)
	}

	def condStep(conf : Configuration, cond : Condition) : Condition = cond match {
		case InstanceOf(expr@New(cls, _), className) if isValue(expr) =>
			Bool(cls == className)

		case InstanceOf(expr, className) =>
			InstanceOf(eStep(conf, expr), className)

		case HasLabel(addr, label) =>
	}


}
