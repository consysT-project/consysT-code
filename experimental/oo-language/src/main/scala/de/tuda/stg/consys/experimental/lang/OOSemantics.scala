package de.tuda.stg.consys.experimental.lang

/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
trait OOSemantics extends LocalSemantics { self : OOSyntax =>

	protected def thisVar : VarId

	trait OOReduction extends Reduction {

		override def reduceExpr(vars : VarStore, expr : Expression) : Expression = expr match {
			case Nix => sys.error("Never evaluate this")
			case _ => super.reduceExpr(vars, expr)
		}

		override def reduceStmt(vars : VarStore, stack : ProgramStack, stmt : Statement) : (VarStore, ProgramStack, Statement) = stmt match {
			case Return(value : Value) => stack match {
				case Nil => throw UnreducableStatement(stmt)
				case (oldVars, Continuation(x, oldStmt)) :: rest => (oldVars + (x -> value), rest, oldStmt)
			}

			case Return(expr) => (vars, stack, Return(reduceExpr(vars, expr)))

			case New(loc, fields, methods, cc@Continuation(x, body)) => fields.find(t => !t._2.isInstanceOf[Value]) match {
				// All fields are evaluated
				case None =>
					val newObj = OObject(fields.mapValues(expr => expr.asInstanceOf[Value]), methods)
					objStore.bind(loc, newObj)
					(vars + (x -> Loc(loc)), stack, body)
				//There are some more fields to evaluate
				case Some((fld, expr)) =>
					(vars, stack, New(loc, fields + (fld -> reduceExpr(vars, expr)), methods, cc))
			}

			case FieldSet(Loc(addr), field, value : Value, Continuation(x, next)) =>
				val OObject(fields, methods) = objStore.lookup(addr)
				val newObj = OObject(fields + (field -> value), methods)
				objStore.bind(addr, newObj)
				(vars + (x -> Nix), stack, next)

			case FieldSet(objExpr : Value, field, expr, body) =>
				(vars, stack, FieldSet(objExpr, field, reduceExpr(vars, expr), body))

			case FieldSet(objExpr, field, expr, body) =>
				(vars, stack, FieldSet(reduceExpr(vars, objExpr), field, expr, body))


			case FieldGet(Loc(addr), field, Continuation(x, next)) =>
				val loc = objStore.lookup(addr).fields(field)
				(vars + (x -> loc), stack, next)

			case FieldGet(objExpr, field, cc) =>
				(vars, stack, FieldGet(reduceExpr(vars, objExpr), field, cc))


			case Invoke(thisLoc@Loc(addr), method, param : Value, cc) =>
				val MethodDef(arg, body) = objStore.lookup(addr).methods(method)
				(Map.empty + (arg -> param) + (thisVar -> thisLoc), ((vars, cc)) :: stack, body)

			case Invoke(objExpr : Value, method, param, cc) =>
				(vars, stack, Invoke(objExpr, method, reduceExpr(vars, param), cc))

			case Invoke(objExpr, method, param, cc) =>
				(vars, stack, Invoke(reduceExpr(vars, objExpr), method, param, cc))

			case _ => super.reduceStmt(vars, stack, stmt)
		}
	}




}
