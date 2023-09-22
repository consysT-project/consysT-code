package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, MutabilityType}

sealed trait Expression

case class Num(n: Int) extends Expression

case object True extends Expression

case object False extends Expression

case object UnitLiteral extends Expression

case class Ref(classType: ClassType, l: ConsistencyType, m: MutabilityType) extends Expression

case class LocalObj(classType: ClassType, constructor: Map[FieldId, Expression], l: ConsistencyType, m: MutabilityType) extends Expression

case class Var(id: VarId) extends Expression

case class Equals(e1: Expression, e2: Expression) extends Expression

case class Add(e1: Expression, e2: Expression) extends Expression
