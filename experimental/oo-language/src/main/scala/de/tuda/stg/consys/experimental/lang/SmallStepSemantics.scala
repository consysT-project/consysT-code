package de.tuda.stg.consys.experimental.lang

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait SmallStepSemantics { self : Syntax =>



	type ProgramStack = List[(VarStore, CCStatement)]
	type VarStore = Map[VarId, Value]

	def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
//
		case Nix => sys.error("Never evaluate this")
		case Var(x) if vars.contains(x) => vars(x)
		case _ => throw UnreducableExpression(expr)

//		case FieldGet(fld) => thisObj match {
//			case obj :: _ => obj.fields(fld)
//		}

//		case FieldSet(fld, value : Value) => thisObj match {
//			case obj :: _ => Obj(obj.fields + (fld -> value), obj.methods)
//		}
//		case FieldSet(fld, expr) => FieldSet(fld, reduceExpr(expr))
	}

	case class UnreducableStatement(stmt : CCStatement) extends Exception(s"unreducable statement: $stmt")
	case class UnreducableExpression(expr : Expression) extends Exception(s"unreducable expression: $expr")

	def reduceStmt(objs : ObjectStore, vars : VarStore, stack : ProgramStack, stmt : CCStatement) : (ObjectStore, VarStore, ProgramStack, CCStatement) = stmt match {
		case CCReturn(value : Value) => stack match {
			case Nil => throw UnreducableStatement(stmt)
			case (oldVars, Continuation(x, oldStmt)) :: rest => (objs, oldVars + (x -> value), rest, oldStmt)
		}

		case CCReturn(expr) => (objs, vars, stack, CCReturn(reduceExpr(vars, expr)))


		case CCNew(loc, fields, methods, cc@Continuation(x, body)) => fields.find(t => t._2.isInstanceOf[Value]) match {
			// All fields are evaluated
			case None =>
				val newObj = Obj(fields.mapValues(expr => expr.asInstanceOf[Value]), methods)
				(objs + (loc -> newObj), vars + (x -> Loc(loc)), stack, body)
			//There are some more fields to evaluate
			case Some((fld, expr)) =>
				(objs, vars, stack, CCNew(loc, fields + (fld -> reduceExpr(vars, expr)), methods, cc))
		}

		case CCFieldSet(Loc(addr), field, value : Value, Continuation(x, next)) =>
			val obj@Obj(fields, methods) = objs(addr)
			val newObj = Obj(fields + (field -> value), methods)
			(objs + (addr -> newObj), vars + (x -> Nix), stack, next)

		case CCFieldSet(objExpr : Value, field, expr, body) =>
			(objs, vars, stack, CCFieldSet(objExpr, field, reduceExpr(vars, expr), body))

		case CCFieldSet(objExpr, field, expr, body) =>
			(objs, vars, stack, CCFieldSet(reduceExpr(vars, objExpr), field, expr, body))


		case CCFieldGet(Loc(addr), field, Continuation(x, next)) =>
			val loc = objs(addr).fields(field)
			(objs, vars + (x -> loc), stack, next)

		case CCFieldGet(objExpr, field, cc) =>
			(objs, vars, stack, CCFieldGet(reduceExpr(vars, objExpr), field, cc))


		case CCInvoke(Loc(addr), method, param : Value, cc) =>
			val MethodDef(arg, body) = objs(addr).methods(method)
			(objs, Map.empty + (arg -> param), ((vars, cc)) :: stack, body)

		case CCInvoke(objExpr : Value, method, param, cc) =>
			(objs, vars, stack, CCInvoke(objExpr, method, reduceExpr(vars, param), cc))

		case CCInvoke(objExpr, method, param, cc) =>
			(objs, vars, stack, CCInvoke(reduceExpr(vars, objExpr), method, param, cc))

	}


}
