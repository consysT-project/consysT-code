package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, Context, FuncDecl, Sort, Expr => Z3Expr}
import de.tuda.consys.invariants.solver.next.ir.{ClassTable, Expressions}
import de.tuda.consys.invariants.solver.next.ir.Classes._
import de.tuda.consys.invariants.solver.next.ir.Expressions.TypedLang
import de.tuda.consys.invariants.solver.next.translate.CompileErrors.CompileException
import TypedLang._
import de.tuda.consys.invariants.solver.next.translate.RepTable.QueryMethodRep

import scala.collection.immutable.Map
trait ExpressionCompiler {

	/** Compiles an IRExpr to a Z3 expr, given the starting state s0 and ending in the 2nd element return state.  */
	def compile[S <: Sort](expr : Expr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repMapBuilder: RepMapBuilder, classTable : ClassTable[Expr]) : (Z3Expr[_], Z3Expr[S]) = {
		throw new CompileException("unknown expression: " + expr)
	}

}

object ExpressionCompiler {

	class BaseExpressionCompiler extends ExpressionCompiler {
		override def compile[S <: Sort](expr : Expr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repMapBuilder: RepMapBuilder, classTable : ClassTable[Expr]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case IRNum(value, typ) => (ctx.mkInt(value), s0)
			case IRTrue(typ) => (ctx.mkTrue(), s0)
			case IRFalse(typ) => (ctx.mkFalse(), s0)
			case IRString(s, typ) => (ctx.mkString(s), s0)
			case IRUnit(typ) =>
				val unitSort = repMapBuilder.getClassSort("Unit", Seq()).getOrElse(CompileErrors.classNotFound("Unit"))
				(ctx.mkConst("unit", unitSort), s0)

			case IRVar(x, typ) => (vars.getOrElse(x, CompileErrors.varNotFound(x)), s0)

			case IREquals(e1, e2, typ) =>
				val (expr1 : Z3Expr[Sort], s1) = compile(e1, vars, s0).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]
				val (expr2 : Z3Expr[Sort], s2) = compile(e2, vars, s1).asInstanceOf[(Z3Expr[Sort], Z3Expr[S])]

				(ctx.mkEq(expr1, expr2), s2)

			case IRLet(id, namedExpr, body, typ) =>
				val (namedVal, s1) = compile(namedExpr, vars, s0)
				val (bodyVal, s2) = compile(body, vars + (id -> namedVal), s1)
				(bodyVal, s2)

			case IRIf(conditionExpr, thenExpr, elseExpr, typ) =>
				val (condVal, s1) = compile(conditionExpr, vars, s0)
				val (thenVal, s2a) = compile(thenExpr, vars, s1)
				val (elseVal, s2b) = compile(elseExpr, vars, s1)

				if (s2a != s1) throw new CompileException("state can not change in then-branch")
				if (s2b != s1) throw new CompileException("state can not change in else-branch")

				(ctx.mkITE(condVal.asInstanceOf[Z3Expr[BoolSort]], thenVal, elseVal), s2b)

			case _ => super.compile(expr, vars, s0)
		}
	}

	class ClassExpressionCompiler(classId : ClassId,  typeArguments : Seq[Sort]) extends BaseExpressionCompiler {
		override def compile[S <: Sort](expr : Expr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repMapBuilder: RepMapBuilder, classTable : ClassTable[Expr]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case IRGetField(fieldId, typ) =>
				val fieldRep = repMapBuilder.getField(classId, typeArguments, fieldId)
					.getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				(ctx.mkApp(fieldRep.funcDecl, s0), s0)

			case IRThis(typ) => (s0, s0)

			case IRCallQuery(recvExpr, methodId, arguments, typ) =>
				val (recvVal, recvState) = compile(recvExpr, vars, s0)


				// Compile the arguments
				var s1 = recvState
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}

				val declaredArguments = declaredArgumentsBuilder.result()
				val actualArguments = Seq(recvVal) ++ declaredArguments


				// Retrieve the correct method
				val recvType = recvExpr.typ

				val methodRep = recvType match {
					case ClassType(recvClassId, recvTypeArguments) =>
						repMapBuilder.getMethod(recvClassId, declaredArguments.map(e => e.getSort.asInstanceOf[Sort]), methodId)
							.getOrElse(CompileErrors.methodNotFound(recvClassId, methodId))
					case TypeVar(typeVarId) =>
						throw new CompileException(s"query call on type variable: $expr")
				}

				// Create the application to the methods function declaration
				methodRep match {
					case QueryMethodRep(funcDecl) =>
						val mthdApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
						(mthdApp, s1)
					case _ => throw new CompileException("method is not a query: " + methodId)
				}

			case _ => super.compile(expr, vars, s0)
		}
	}

	class MutableClassExpressionCompiler(classId : ClassId, typeArguments : Seq[Sort]) extends ClassExpressionCompiler(classId, typeArguments) {
		override def compile[S <: Sort](expr : Expr, vars : Map[VarId, Z3Expr[_]], s0 : Z3Expr[S])(implicit ctx : Context, repTable : RepMapBuilder, classTable : ClassTable[Expr]) : (Z3Expr[_], Z3Expr[S]) = expr match {
			case IRSetField(fieldId, newVal, typ) =>
				val (valExpr, s1) = compile(newVal, vars, s0)

				val fieldRep = repTable
					.getField(classId, typeArguments, fieldId)
					.getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				val newState = ctx.mkUpdateField[Sort, S](fieldRep.funcDecl.asInstanceOf[FuncDecl[Sort]], s1, valExpr.asInstanceOf[Z3Expr[Sort]]) //ctx.mkApp(constructorDecl, arguments : _*)
				(valExpr, newState)


			case IRCallUpdateThis(methodId, arguments, typ) =>
				var s1 = s0
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}

				val declaredArguments = declaredArgumentsBuilder.result()

				val methodRep = repTable.getMethod(classId, typeArguments, methodId)
					.getOrElse(CompileErrors.methodNotFound(classId, methodId))


//				methodRep match {
//					case UpdateMethodRep(funcDecl) =>
//						val actualArguments = Seq(s1) ++ declaredArguments
//						val mthdApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
//						val unitRep = repTable.getOrElse("Unit", CompileErrors.classNotFound("Unit"))
//						(ctx.mkConst("unit", unitRep.sortFactory), mthdApp.asInstanceOf[Z3Expr[S]])
//					case _ => throw new CompileException("method is not an update: " + methodId)
//				}
			???


			case IRCallUpdateField(fieldId, methodId, arguments, typ) =>
				var s1 = s0
				val declaredArgumentsBuilder = Seq.newBuilder[Z3Expr[_]]
				for (arg <- arguments) {
					val (argVal, argState) = compile(arg, vars, s1)
					declaredArgumentsBuilder.addOne(argVal)
					s1 = argState
				}
				val declaredArguments = declaredArgumentsBuilder.result()

				val fieldRep = repTable
					.getField(classId, typeArguments, fieldId)
					.getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

				val fieldDecl = classTable
					.getOrElse(classId, CompileErrors.classNotFound(classId))
					.getField(fieldId).getOrElse(CompileErrors.fieldNotFound(classId, fieldId))

//				val fieldClassRep = repTable
//					.getOrElse(fieldDecl.typ.name, CompileErrors.classNotFound(fieldDecl.typ.name))
//
//				val methodRep = fieldClassRep
//					.getMethod(methodId).getOrElse(CompileErrors.methodNotFound(fieldDecl.typ.name, methodId))
//
//				methodRep match {
//					case UpdateMethodRep(funcDecl) =>
//						val actualArguments = Seq(ctx.mkApp(fieldRep.funcDecl, s1)) ++ declaredArguments
//						val methodApp = ctx.mkApp(funcDecl, actualArguments.toArray : _*)
//						val updateField = ctx.mkUpdateField(fieldRep.funcDecl.asInstanceOf[FuncDecl[Sort]], s1, methodApp.asInstanceOf[Z3Expr[Sort]])
//						val unitRep = repTable.getOrElse("Unit", CompileErrors.classNotFound("Unit"))
//						(ctx.mkConst("unit", unitRep.sortFactory), updateField)
//					case _ => throw new CompileException("method is not an update: " + methodId)
//				}

			???

			case _ => super.compile(expr, vars, s0)
		}
	}
}

