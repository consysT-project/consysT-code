package de.tuda.stg.consys.experimental.lang

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait LocalSemantics { self : Syntax =>

	/* Object store */
	type ObjectStore = Map[Location, Obj]

	/* Stored in the store */
	type Obj = OObject[FieldId, Value, MethodId, MethodDef]

	/* Call stack of the program */
	type ProgramStack = List[(VarStore, Continuation)]

	/* Variable store */
	type VarStore = Map[VarId, Value]

	case class UnreducableStatement(stmt : Statement) extends Exception(s"unreducable statement: $stmt")
	case class UnreducableExpression(expr : Expression) extends Exception(s"unreducable expression: $expr")


	def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
		case Var(x) if vars.contains(x) => vars(x)
		case _ => throw UnreducableExpression(expr)
	}


	def reduceStmt(objs : ObjectStore, vars : VarStore, stack : ProgramStack, stmt : Statement) : (ObjectStore, VarStore, ProgramStack, Statement) = stmt match {
		case Return(value : Value) => stack match {
			case Nil => throw UnreducableStatement(stmt)
			case (oldVars, Continuation(x, oldStmt)) :: rest => (objs, oldVars + (x -> value), rest, oldStmt)
		}

		case Return(expr) => (objs, vars, stack, Return(reduceExpr(vars, expr)))

		case Bind(value : Value, Continuation(x, next)) =>
			(objs, vars + (x -> value), stack, next)

		case Bind(expr, cc) =>
			(objs, vars, stack, Bind(reduceExpr(vars, expr), cc))

		case _ => throw UnreducableStatement(stmt)
	}

	def obj(fields : Map[FieldId, Value], methods : Map[MethodId, MethodDef]) : Obj = OObject(fields, methods)

}
