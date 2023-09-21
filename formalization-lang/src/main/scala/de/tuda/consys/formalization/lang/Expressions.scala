package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types2.{ClassType, ConsistencyType}

sealed trait Expression

case class Num(n: Int) extends Expression

case object True extends Expression

case object False extends Expression

case object UnitLiteral extends Expression

case class Ref(classType: ClassType, l: ConsistencyType, m: ConsistencyType) extends Expression

case class LocalObj(classType: ClassType, e: Seq[Expression], l: ConsistencyType, m: ConsistencyType) extends Expression

case class Var(id: VarId) extends Expression

case class Equals(expr1: Expression, expr2: Expression) extends Expression

case class Add(expr1: Expression, expr2: Expression) extends Expression
