package de.tuda.stg.consys.experimental.lang

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait OOSemantics extends LocalSemantics { self : OOSyntax =>



	override def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
		case Nix => sys.error("Never evaluate this")
		case _ => super.reduceExpr(vars, expr)
	}



	override def reduceStmt(objs : ObjectStore, vars : VarStore, stack : ProgramStack, stmt : Statement) : (ObjectStore, VarStore, ProgramStack, Statement) = stmt match {
		case Return(value : Value) => stack match {
			case Nil => throw UnreducableStatement(stmt)
			case (oldVars, Continuation(x, oldStmt)) :: rest => (objs, oldVars + (x -> value), rest, oldStmt)
		}

		case Return(expr) => (objs, vars, stack, Return(reduceExpr(vars, expr)))


		case New(loc, fields, methods, cc@Continuation(x, body)) => fields.find(t => !t._2.isInstanceOf[Value]) match {
			// All fields are evaluated
			case None =>
				val newObj = OObject(fields.mapValues(expr => expr.asInstanceOf[Value]), methods)
				(objs + (loc -> newObj), vars + (x -> Loc(loc)), stack, body)
			//There are some more fields to evaluate
			case Some((fld, expr)) =>
				(objs, vars, stack, New(loc, fields + (fld -> reduceExpr(vars, expr)), methods, cc))
		}

		case FieldSet(Loc(addr), field, value : Value, Continuation(x, next)) =>
			val OObject(fields, methods) = objs(addr)
			val newObj = OObject(fields + (field -> value), methods)
			(objs + (addr -> newObj), vars + (x -> Nix), stack, next)

		case FieldSet(objExpr : Value, field, expr, body) =>
			(objs, vars, stack, FieldSet(objExpr, field, reduceExpr(vars, expr), body))

		case FieldSet(objExpr, field, expr, body) =>
			(objs, vars, stack, FieldSet(reduceExpr(vars, objExpr), field, expr, body))


		case FieldGet(Loc(addr), field, Continuation(x, next)) =>
			val loc = objs(addr).fields(field)
			(objs, vars + (x -> loc), stack, next)

		case FieldGet(objExpr, field, cc) =>
			(objs, vars, stack, FieldGet(reduceExpr(vars, objExpr), field, cc))


		case Invoke(Loc(addr), method, param : Value, cc) =>
			val MethodDef(arg, body) = objs(addr).methods(method)
			(objs, Map.empty + (arg -> param), ((vars, cc)) :: stack, body)

		case Invoke(objExpr : Value, method, param, cc) =>
			(objs, vars, stack, Invoke(objExpr, method, reduceExpr(vars, param), cc))

		case Invoke(objExpr, method, param, cc) =>
			(objs, vars, stack, Invoke(reduceExpr(vars, objExpr), method, param, cc))


		case _ => super.reduceStmt(objs, vars, stack, stmt)

	}

	def reduceAllStmt(stmt : Statement, objs : ObjectStore = Map(), vars : VarStore = Map(), stack : ProgramStack = Nil) : (ObjectStore, VarStore, ProgramStack, Statement) = {
		var o = objs
		var v = vars
		var s = stack
		var st = stmt
		try {
			while (true) {
				val (_o, _v, _s, _st) = reduceStmt(o, v, s, st)
				o = _o; v = _v; s = _s; st = _st
			}
		} catch {
			case UnreducableStatement(_) | UnreducableExpression(_) =>
				return (o, v, s, st)
		}

		sys.error("Reached unreachable code")
	}


}
