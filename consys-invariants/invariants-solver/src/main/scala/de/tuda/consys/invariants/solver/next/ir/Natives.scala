package de.tuda.consys.invariants.solver.next.ir

import com.microsoft.z3.{Expr, SeqSort, Sort}
import de.tuda.consys.invariants.solver.next.ir.IR.{NativeClassDecl, NativeQueryMethodDecl}

object Natives {

	val INT_CLASS = NativeClassDecl("Int",
		ctx => ctx.getIntSort,
		Map()
	)
	val INT_TYPE = INT_CLASS.toType


	val BOOL_CLASS = NativeClassDecl("Bool",
		ctx => ctx.getBoolSort,
		Map()
	)
	val BOOL_TYPE = BOOL_CLASS.toType


	val UNIT_CLASS = NativeClassDecl("Unit",
		ctx => ctx.mkTupleSort(ctx.mkSymbol("Unit"), Array(), Array()),
		Map()
	)
	val UNIT_TYPE = UNIT_CLASS.toType


	val STRING_CLASS = NativeClassDecl("String",
		ctx => ctx.getStringSort,
		Map(
			"length" -> NativeQueryMethodDecl("length", Seq(), INT_TYPE, (ctx, recv, args) => {
				ctx.mkLength(recv.asInstanceOf[Expr[SeqSort[Sort]]])
			})
		)
	)
	val STRING_TYPE = STRING_CLASS.toType
}
