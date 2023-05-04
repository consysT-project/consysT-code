package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, Context, FuncDecl, Sort, Expr => Z3Expr}
import de.tuda.consys.invariants.solver.next.ir.IR._
import de.tuda.consys.invariants.solver.next.translate.CompileErrors.CompileException
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.{QueryMethodRep, UpdateMethodRep}
trait ExpressionCompiler {

	/** Compiles an IRExpr to a Z3 expr, given the starting state s0 and ending in the 2nd element return state.  */
	def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repTable : RepTable, classTable : ClassTable) : (Z3Expr[_], Z3Expr[S]) = {
		throw new CompileException("unknown expression: " + expr)
	}

}

object ExpressionCompiler {

	class BaseExpressionCompiler extends ExpressionCompiler {
		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repTable : RepTable, classTable : ClassTable) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case Num(n) => (ctx.mkInt(n), s0)
			case True => (ctx.mkTrue(), s0)
			case False => (ctx.mkFalse(), s0)
			case Str(s) => (ctx.mkString(s), s0)
			case UnitLiteral =>
				val unitRep = repTable.getOrElse("Unit", CompileErrors.classNotFound("Unit"))
				(ctx.mkConst("unit", unitRep.sort), s0)

			case Var(x) => (vars.getOrElse(x, CompileErrors.varNotFound(x)), s0)

			case Equals(e1, e2) =>
				val (expr1 : Z3Expr[Sort], s1) = compile(e1, vars, s0).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]
				val (expr2 : Z3Expr[Sort], s2) = compile(e2, vars, s1).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]

				(ctx.mkEq(expr1, expr2), s2)

			case Let(id, namedExpr, body) =>
				val (namedVal, s1) = compile(namedExpr, vars, s0)
				val (bodyVal, s2) = compile(body, vars + (id -> namedVal), s1)
				(bodyVal, s2)

			case If(conditionExpr, thenExpr, elseExpr) =>
				val (condVal, s1) = compile(conditionExpr, vars, s0)
				val (thenVal, s2a) = compile(thenExpr, vars, s1)
				val (elseVal, s2b) = compile(elseExpr, vars, s1)

				if (s2a != s1) throw new CompileException("state can not change in then-branch")
				if (s2b != s1) throw new CompileException("state can not change in else-branch")

				(ctx.mkITE(condVal.asInstanceOf[Z3Expr[BoolSort]], thenVal, elseVal), s2b)

			case _ => super.compile(expr, vars, s0)
		}
	}

	class ClassExpressionCompiler(classId : ClassId) extends BaseExpressionCompiler {
		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repTable : RepTable, classTable : ClassTable) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case GetField(fieldId) =>
				val fieldRep = repTable
					.getOrElse(classId, CompileErrors.classNotFound(classId))
					.getField(fieldId).getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				(ctx.mkApp(fieldRep.funcDecl, s0), s0)

			case This => (s0, s0)

			case CallQuery(recvExpr, methodId, arguments) =>
				val (recvVal, recvState) = compile(recvExpr, vars, s0)

				var s1 = recvState
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}

				val declaredArguments = declaredArgumentsBuilder.result()
				val actualArguments = Seq(recvVal) ++ declaredArguments

				val (recvClassId, recvClassRep) = sortToClassRep(repTable, recvVal.getSort.asInstanceOf[Sort])
					.getOrElse(throw new CompileException())

				val methodRep = recvClassRep.getMethod(methodId).getOrElse(CompileErrors.methodNotFound(recvClassId, methodId))

				methodRep match {
					case QueryMethodRep(funcDecl) =>
						val mthdApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
						(mthdApp, s1)
					case _ => throw new CompileException("method is not a query: " + methodId)
				}

			case _ => super.compile(expr, vars, s0)
		}
	}

	class MutableClassExpressionCompiler(classId : ClassId) extends ClassExpressionCompiler(classId) {
		override def compile[S <: Sort](expr : IRExpr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repTable : RepTable, classTable : ClassTable) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case SetField(fieldId, newVal) =>
				val (valExpr, s1) = compile(newVal, vars, s0)

				val fieldRep = repTable
					.getOrElse(classId, CompileErrors.classNotFound(classId))
					.getField(fieldId).getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				val newState = ctx.mkUpdateField[Sort, S](fieldRep.funcDecl.asInstanceOf[FuncDecl[Sort]], s1, valExpr.asInstanceOf[Z3Expr[Sort]]) //ctx.mkApp(constructorDecl, arguments : _*)
				(valExpr, newState)


			case CallUpdateThis(methodId, arguments) =>
				var s1 = s0
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}

				val declaredArguments = declaredArgumentsBuilder.result()

				val classRep = repTable.getOrElse(classId, CompileErrors.classNotFound(classId))

				val methodRep = classRep.getMethod(methodId)
					.getOrElse(CompileErrors.methodNotFound(classId, methodId))

				methodRep match {
					case UpdateMethodRep(funcDecl) =>
						val actualArguments = Seq(s1) ++ declaredArguments
						val mthdApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
						val unitRep = repTable.getOrElse("Unit", CompileErrors.classNotFound("Unit"))
						(ctx.mkConst("unit", unitRep.sort), mthdApp.asInstanceOf[Z3Expr[S]])
					case _ => throw new CompileException("method is not an update: " + methodId)
				}


			case CallUpdateField(fieldId, methodId, arguments) =>
				var s1 = s0
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}
				val declaredArguments = declaredArgumentsBuilder.result()

				val fieldRep = repTable
					.getOrElse(classId, CompileErrors.classNotFound(classId))
					.getField(fieldId).getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				val fieldDecl = classTable
					.getOrElse(classId, CompileErrors.classNotFound(classId))
					.getField(fieldId).getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				val fieldClassRep = repTable
					.getOrElse(fieldDecl.typ.name, CompileErrors.classNotFound(fieldDecl.typ.name))

				val methodRep = fieldClassRep
					.getMethod(methodId).getOrElse(CompileErrors.methodNotFound(fieldDecl.typ.name, methodId))

				methodRep match {
					case UpdateMethodRep(funcDecl) =>
						val actualArguments = Seq(ctx.mkApp(fieldRep.funcDecl, s1)) ++ declaredArguments
						val methodApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
						val updateField = ctx.mkUpdateField(fieldRep.funcDecl.asInstanceOf[FuncDecl[Sort]], s1, methodApp.asInstanceOf[Z3Expr[Sort]])
						val unitRep = repTable.getOrElse("Unit", CompileErrors.classNotFound("Unit"))
						(ctx.mkConst("unit", unitRep.sort), updateField)
					case _ => throw new CompileException("method is not an update: " + methodId)
				}


			case _ => super.compile(expr, vars, s0)
		}
	}
}
