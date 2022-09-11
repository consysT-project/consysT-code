package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, DatatypeSort, Sort, TupleSort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.ClassDef.FieldDef
import de.tuda.stg.consys.invariants.lang.TypeSystem.TypeMap
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement, Type}
import de.tuda.stg.consys.invariants.lang.{ClassDef, ClassTable, TypeSystem}
import org.sosy_lab.java_smt.api.{Formula, SolverContext}


class Translator(val context : Z3Context) {

	private case class TranslationError(msg : String) extends Exception(msg)

	private def error(msg : String) : Nothing =
		throw TranslationError(msg)

	def translateType(typ : Type) : Sort = typ match {
		case TBool => context.getBoolSort
		case TInt => context.getIntSort
		case TUnit => context.mkSeqSort(context.getIntSort)
		case TRef(c) => ???
		case TPair(t1, t2) => ???
		case TSet(t) => context.mkSetSort(translateType(t))
		case TString => context.getStringSort
	}

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
			val sort = translateType(typ)
			context.mkConst(x, sort)

		case EField(f) => ???

		case ELet(x, namedExpr, body) => ???

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

	def translateClass(clsDef : ClassDef) : TupleSort = {
		val clsName = context.mkSymbol(clsDef.name)

		val (fieldSymbols, fieldSorts) = clsDef.fields.map(f => (context.mkSymbol(f.name), translateType(f.typ))).unzip

		context.mkTupleSort(clsName,
			fieldSymbols.toArray, fieldSorts.toArray
		)
	}
}

object Translator {

	System.load("/usr/lib/jni/libz3.so")
	System.load("/usr/lib/jni/libz3java.so")

	def main(args : Array[String]) : Unit = {

		val expr = EPlus(VInt(42), VInt(23))()
		val typeResult = TypeSystem.checkExpr(ClassTable(), Map(), expr)

		val z3Ctx = new Z3Context()
		val trans = new Translator(z3Ctx)

		val c = ClassDef("User", Seq(FieldDef(TString, "name"), FieldDef(TInt, "amount")), Seq())

		val z3Cls = trans.translateClass(c)

		val z3Expr = trans.translateExpression(typeResult.typeMap, expr)
		println(z3Expr)

	}
}
