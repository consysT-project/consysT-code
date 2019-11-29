package de.tuda.stg.consys.experimental.lang

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait LocalSemantics { self : Syntax =>

	/* Object store */
	type ObjectStore <: de.tuda.stg.consys.experimental.lang.ObjectStore[Location, Obj]

	/* Stored in the store */
	type Obj = OObject[FieldId, Value, MethodId, MethodDef]

	/* Call stack of the program */
	type ProgramStack = List[(VarStore, Continuation)]

	/* Variable store */
	type VarStore = Map[VarId, Value]



	protected def createReduction : Reduction


	def obj(fields : Map[FieldId, Value], methods : Map[MethodId, MethodDef]) : Obj = OObject(fields, methods)

	def reduce(stmt : Statement) : Statement = {
		val exec = createReduction
		val (_, _, result) = exec.reduceAllStmt(stmt)
		result
	}

	case class UnreducableStatement(stmt : Statement) extends Exception(s"unreducable statement: $stmt")
	case class UnreducableExpression(expr : Expression) extends Exception(s"unreducable expression: $expr")



	protected trait Reduction {

		protected def objStore : ObjectStore

		def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
			case Var(x) if vars.contains(x) => vars(x)
			case _ => throw UnreducableExpression(expr)
		}


		def reduceStmt(vars : VarStore, stack : ProgramStack, stmt : Statement) : (VarStore, ProgramStack, Statement) = stmt match {
			case Return(value : Value) => stack match {
				case Nil => throw UnreducableStatement(stmt)
				case (oldVars, Continuation(x, oldStmt)) :: rest => (oldVars + (x -> value), rest, oldStmt)
			}

			case Return(expr) => (vars, stack, Return(reduceExpr(vars, expr)))

			case Bind(value : Value, Continuation(x, next)) =>
				(vars + (x -> value), stack, next)

			case Bind(expr, cc) =>
				(vars, stack, Bind(reduceExpr(vars, expr), cc))

			case _ => throw UnreducableStatement(stmt)
		}

		def reduceAllStmt(stmt : Statement, vars : VarStore = Map(), stack : ProgramStack = Nil) : (VarStore, ProgramStack, Statement) = {
			var v = vars
			var s = stack
			var st = stmt
			try {
				while (true) {
					val (_v, _s, _st) = reduceStmt(v, s, st)
					v = _v; s = _s; st = _st
				}
			} catch {
				case e : UnreducableStatement =>
					println("Finished reduction: " + e.getMessage)
					println(objStore)
					return (v, s, st)
			}

			sys.error("Reached unreachable code")
		}
	}






}
