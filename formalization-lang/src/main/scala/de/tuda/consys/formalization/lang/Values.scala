package de.tuda.consys.formalization.lang

sealed trait Value

case class NumV(n: Int) extends Value

case class BoolV(b: Boolean) extends Value

case class RefV(objectId: String, classId: ClassId, consistency: ConsistencyType) extends Value

case object UnitV extends Value
