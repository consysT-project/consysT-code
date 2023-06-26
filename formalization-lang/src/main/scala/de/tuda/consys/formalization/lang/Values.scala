package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ConsistencyType

sealed trait Value

case class NumV(n: Int) extends Value

case class BoolV(b: Boolean) extends Value

case class RefV(objectId: String, classId: ClassId, consistency: ConsistencyType) extends Value

case object UnitV extends Value
