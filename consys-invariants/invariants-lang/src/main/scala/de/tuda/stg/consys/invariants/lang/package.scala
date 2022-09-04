package de.tuda.stg.consys.invariants

import de.tuda.stg.consys.invariants.lang.Expr.{Val, Var}

package object lang {

	type VarId = String
	type FieldId = String
	type ClassId = String
	type MethodId = String
	type RefId = String

	type VarEnv = Map[VarId, Val]
	type ClsTable = Map[ClassId, Cls]
	type Store = Map[RefId, Obj]

	case class Obj(c : ClassId, fields : Map[FieldId, Val])

	val thsId : VarId = "$this"
	val thsVar = Var(thsId)



}
