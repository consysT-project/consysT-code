package de.tuda.consys.invariants.solver.next.ir

import com.microsoft.z3.{ArraySort, BoolSort, Expr, SeqSort, SetSort, Sort}
import de.tuda.consys.invariants.solver.next.ir.Classes.{NativeClassDecl, NativeQueryMethodDecl, TypeVar, VarDecl}

object Natives {

	val INT_CLASS = NativeClassDecl("Int",
		Seq(),
		(ctx, sorts) => ctx.getIntSort,
		Map()
	)
	val INT_TYPE = INT_CLASS.toType(Seq())


	val BOOL_CLASS = NativeClassDecl("Bool",
		Seq(),
		(ctx, sorts) => ctx.getBoolSort,
		Map()
	)
	val BOOL_TYPE = BOOL_CLASS.toType(Seq())


	val UNIT_CLASS = NativeClassDecl("Unit",
		Seq(),
		(ctx, sorts) => ctx.mkTupleSort(ctx.mkSymbol("Unit"), Array(), Array()),
		Map()
	)
	val UNIT_TYPE = UNIT_CLASS.toType(Seq())

	val OBJECT_CLASS = NativeClassDecl("Object",
		Seq(),
		(ctx, sorts) => ctx.mkTupleSort(ctx.mkSymbol("Object"), Array(), Array()),
		Map()
	)


	val STRING_CLASS = NativeClassDecl("String",
		Seq(),
		(ctx, sorts) => ctx.getStringSort,
		Map(
			"length" -> NativeQueryMethodDecl("length", Seq(), INT_TYPE, (ctx, recv, args) => {
				ctx.mkLength(recv.asInstanceOf[Expr[SeqSort[Sort]]])
			})
		)
	)
	val STRING_TYPE = STRING_CLASS.toType(Seq())

	val SET_CLASS = NativeClassDecl("Set",
		Seq(TypeVar("A")),
		(ctx, sorts) => ctx.mkSetSort(sorts(0)),
		Map(
			"contains" -> NativeQueryMethodDecl("contains", Seq(VarDecl("x", TypeVar("A"))), BOOL_TYPE, (ctx, recv, args) => {
				ctx.mkSetMembership[Sort](args(0).asInstanceOf[Expr[Sort]], recv.asInstanceOf[Expr[ArraySort[Sort, BoolSort]]])
			})
		)
	)

}
