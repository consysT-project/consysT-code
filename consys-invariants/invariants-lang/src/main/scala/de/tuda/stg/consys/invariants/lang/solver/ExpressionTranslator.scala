package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, Sort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.ClassDef.FieldDef
import de.tuda.stg.consys.invariants.lang.TypeSystem.TypeMap
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.{ClassDef, ClassTable, TypeSystem, VarId}


trait ExpressionTranslator { this : BaseTranslator with TypeTranslator =>

	private def constForVar(x : VarId, sort : Sort) : Z3Expr[_] =
		context.mkConst(x, sort)

	def translateExpression(typeMap : TypeMap, expr : Expression) : Z3Expr[_] = expr match {
		case VUnit => context.mkUnit(context.mkEmptySeq(context.getIntSort))
		case VBool(b) => context.mkBool(b)
		case VInt(i) => context.mkInt(i)
		case VSet(typ, xs) => ???
		case VPair(x1, x2) => ???
		case VRef(c, ref) => ???
		case VString(s) => context.mkString(s)

		case EVar(x) =>
			val typ = typeMap.getOrElse(expr.nodeId, error(s"type for $expr cannot be resolved"))
			constForVar(x, translateType(typ))

		case EField(f) => ???

		case ELet(x, namedExpr, body) =>
			val typ = typeMap.getOrElse(namedExpr.nodeId, error(s"type for $x cannot be resolved"))
			val xConst = context.mkConst(x, translateType(typ))
			val z1 = translateExpression(typeMap, namedExpr)
			val z2 = translateExpression(typeMap, body)

			z2.substitute(xConst, z1)


		case EPair(e1, e2) =>
			val z1 = translateExpression(typeMap, e1)
			val z2 = translateExpression(typeMap, e2)

			???


		case EPlus(e1, e2) =>
			val z1 = translateExpression(typeMap, e1).asInstanceOf[Z3Expr[ArithSort]]
			val z2 = translateExpression(typeMap, e2).asInstanceOf[Z3Expr[ArithSort]]
			context.mkAdd(z1, z2)

		case EFst(e) =>	???

		case ESnd(e) => ???
	}

	def translateStatement(typeMap : TypeMap, stmt : Statement) : Z3Expr[_] = stmt match {
		case Return(expr) =>
			translateExpression(typeMap, expr)

		case DoNew(x, cls, fields, body) =>
			???

	}


}

object ExpressionTranslator {


	def main(args : Array[String]) : Unit = {

		val expr = EPlus(VInt(42), VInt(23))()
		val typeResult = TypeSystem.checkExpr(ClassTable(), Map(), expr)

		val z3Ctx = new Z3Context()

		val translator = new BaseTranslator with TypeTranslator with ClassTableTranslator with ExpressionTranslator {
			override def context : Z3Context = z3Ctx
		}

		val c = ClassDef("User", Seq(FieldDef(TString, "name"), FieldDef(TInt, "amount")), Seq())

		val z3Cls = translator.translateClass(c)

		val z3Expr = translator.translateExpression(typeResult.typeMap, expr)
		println(z3Expr)

	}
}
