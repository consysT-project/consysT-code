package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Cls.{FieldDef, MethodDef}


case class Cls(
	fields : Map[FieldId, FieldDef],
	methods : Map[MethodId, MethodDef]
)

object Cls {

	case class VarDef(t : Type, x : VarId)
	case class FieldDef(t : Type)
	case class MethodDef(t : Type, pars : Seq[VarDef], stmt : Stmt)

}
