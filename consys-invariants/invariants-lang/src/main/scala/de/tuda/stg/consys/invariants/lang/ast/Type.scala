package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.ClassId

sealed trait Type

object Type {
	case object TBool extends Type
	case object TInt extends Type
	case object TUnit extends Type
	case class TRef(c : ClassId) extends Type
	case class TPair(t1 : Type, t2 : Type) extends Type
	case class TSet(t : Type) extends Type
}
