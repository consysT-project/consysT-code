package de.tuda.consys.formalization.lang

sealed trait Expression

sealed trait Literal extends Expression

case class Num(n: Int) extends Literal

case object True extends Literal

case object False extends Literal

case object UnitLiteral extends Literal

case object This extends Expression

case class Var(id: VarId) extends Expression

case class Equals(expr1: Expression, expr2: Expression) extends Expression

case class Add(expr1: Expression, expr2: Expression) extends Expression
