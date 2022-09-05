package de.tuda.stg.consys.invariants

import de.tuda.stg.consys.invariants.lang.Expr.{Val, Var}

package object lang {

	type VarId = String
	type FieldId = String
	type ClassId = String
	type MethodId = String
	type RefId = String

	type ClsTable = Map[ClassId, Cls]


	val thsId : VarId = "$this"
	val thsVar = Var(thsId)


	type TypeEnv = Map[VarId, Type]



}
