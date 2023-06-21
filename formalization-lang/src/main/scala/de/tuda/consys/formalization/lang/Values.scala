package de.tuda.consys.formalization.lang

sealed trait Value

case class NumV(n: Int) extends Value

case class BoolV(b: Boolean) extends Value

case class StringV(s: String) extends Value

case class ObjectV(objectId: String,
                   classId: ClassId,
                   consistency: ConsistencyType,
                   fields: Map[FieldId, Value]
                  ) extends Value with Serializable

case object UnitV extends Value
