package de.tuda.stg.consys.invariants.lang

sealed trait Type

object Type {
	case object TBool extends Type
	case object TInt extends Type
	case object TUnit extends Type
	case class TCls(c : ClassId) extends Type
	case class TPair(t1 : Type, t2 : Type) extends Type
	case class TSet(t : Type) extends Type
}
