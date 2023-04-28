package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{Context, DatatypeSort, FuncDecl, Sort, TupleSort, Expr => Z3Expr}
import de.tuda.consys.invariants.solver.next.ir.IR._
import de.tuda.consys.invariants.solver.next.translate.TypeRep.{NativeTypeRep, ObjectTypeRep}
trait ExpressionCompiler {

	/** Compiles an IRExpr to a Z3 expr, given the starting state s0 and ending in the 2nd element return state.  */
	def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S]) : (Z3Expr[_], Z3Expr[S]) = {
		throw ParseException("unknown expression: " + expr)
	}

}

object ExpressionCompiler {

	class BaseExpressionCompiler(ctx : Context, typeMap : TypeMap) extends ExpressionCompiler {

		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case Num(n) => (ctx.mkInt(n), s0)

			case True => (ctx.mkTrue(), s0)
			case False => (ctx.mkFalse(), s0)


			case Str(s) => (ctx.mkString(s), s0)

			case Var(x) => (vars.getOrElse(x, throw ParseException("variable not found: " + x)), s0)

			case Equals(e1, e2) =>
				val (expr1 : Z3Expr[Sort], s1) = compile(e1, vars, s0).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]
				val (expr2 : Z3Expr[Sort], s2) = compile(e2, vars, s1).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]

				(ctx.mkEq(expr1, expr2), s2)

			case Let(id, namedExpr, body) =>
				val (namedVal, s1) = compile(namedExpr, vars, s0)
				val (bodyVal, s2) = compile(body, vars + (id -> namedVal), s1)
				(bodyVal, s2)

			case _ => super.compile(expr, vars, s0)
		}
	}

	class ObjectClassExpressionCompiler(ctx : Context, typeMap : TypeMap) extends BaseExpressionCompiler(ctx, typeMap) {
		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case GetField(id) =>
				val s0Sort = Z3Utils.asObjectSort(s0.getSort).getOrElse(throw ParseException("expected object sort, but got: " + s0.getSort))
				val fieldAcc = Z3Utils.getObjectField(s0Sort, id).getOrElse(throw ParseException(s"field not found: $id (in class $s0Sort)"))
				(ctx.mkApp(fieldAcc, s0), s0)

			case This => (s0, s0)

			case CallQuery(recv, mthd, arguments) =>
				val (recvVal, recvState) = compile(recv, vars, s0)

				var s1 = recvState
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}

				val declaredArguments = declaredArgumentsBuilder.result()

				val recvType = findRepInTypeMap(typeMap, recvVal.getSort).getOrElse(throw ParseException(s"receiver not found: ${recvVal.getSort}"))

				recvType match {
					case NativeTypeRep(sort) => throw ParseException("native class does not have methods: " + recvType)
					case ObjectTypeRep(sort, accessors, methods) =>
//						methods.getOrElse((mthd, null))
				}

				???



			case _ => super.compile(expr, vars, s0)
		}
	}

	class UpdateBodyExpressionCompiler(ctx : Context, typeMap : TypeMap) extends ObjectClassExpressionCompiler(ctx, typeMap) {
		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case SetField(id, newVal) =>
				val (valExpr, s1) = compile(newVal, vars, s0)

				val s1Sort = Z3Utils.asObjectSort(s1.getSort).getOrElse(throw ParseException("expected object sort, but got: " + s1.getSort))
				val fieldDecl = Z3Utils.getObjectField(s1Sort, id).getOrElse(throw ParseException("field not found: " + id))

//				val constructorDecl = Z3Utils.getObjectConstructor(s1Sort)
//
//				val arguments = Z3Utils.getObjectFields(s1Sort).map(fieldDecl => {
//					val fldName = fieldDecl.getName.toString
//					if (fldName == id) {
//						valExpr
//					} else {
//						ctx.mkApp(fieldDecl, s1)
//					}
//				})

				val newState = ctx.mkUpdateField[Sort, S](fieldDecl.asInstanceOf[FuncDecl[Sort]], s1, valExpr.asInstanceOf[Z3Expr[Sort]]) //ctx.mkApp(constructorDecl, arguments : _*)
				(valExpr, newState)


			case _ => super.compile(expr, vars, s0)
		}
	}
}
