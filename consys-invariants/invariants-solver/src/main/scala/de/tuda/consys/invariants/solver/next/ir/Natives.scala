package de.tuda.consys.invariants.solver.next.ir

import de.tuda.consys.invariants.solver.next.ir.IR.NativeClassDecl

object Natives {

	val INT_CLASS = NativeClassDecl("Int")
	val BOOL_CLASS = NativeClassDecl("Bool")
	val STRING_CLASS = NativeClassDecl("String")
	val UNIT_CLASS = NativeClassDecl("Unit")

	val INT_TYPE = INT_CLASS.toType
	val BOOL_TYPE = BOOL_CLASS.toType
	val STRING_TYPE = STRING_CLASS.toType
	val UNIT_TYPE = UNIT_CLASS.toType


}
