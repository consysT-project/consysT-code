package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, MutabilityType}

sealed trait Expression

case class Num(n: NumericType) extends Expression

trait BooleanValue extends Expression

case object True extends BooleanValue

case object False extends BooleanValue

case object UnitLiteral extends Expression

case class Ref(id: String,
               classType: ClassType,
               l: ConsistencyType,
               m: MutabilityType
              ) extends Expression

case class LocalObj(classType: ClassType,
                    constructor: Map[FieldId, Expression],
                    l: ConsistencyType
                   ) extends Expression

case class Var(id: VarId) extends Expression

case class Equals(e1: Expression,
                  e2: Expression
                 ) extends Expression

sealed trait ArithmeticOperator {
  def apply(x1: Num, x2: Num): Num
}

case object Add extends ArithmeticOperator {
  override def apply(x1: Num, x2: Num): Num = Num(x1.n + x2.n)
}

case object Subtract extends ArithmeticOperator{
  override def apply(x1: Num, x2: Num): Num = Num(x1.n - x2.n)
}

case object Multiply extends ArithmeticOperator{
  override def apply(x1: Num, x2: Num): Num = Num(x1.n * x2.n)
}

case object Divide extends ArithmeticOperator{
  override def apply(x1: Num, x2: Num): Num = Num(if (x2.n != 0) x1.n / x2.n else Int.MaxValue)
}

case class ArithmeticOperation(e1: Expression,
                               e2: Expression,
                               op: ArithmeticOperator
                              ) extends Expression

sealed trait ArithmeticComparator {
  def apply(x1: Num, x2: Num): BooleanValue
}

case object LessThan extends ArithmeticComparator {
  def apply(x1: Num, x2: Num): BooleanValue = if (x1.n < x2.n) True else False
}

case object LessOrEqualThan extends ArithmeticComparator{
  def apply(x1: Num, x2: Num): BooleanValue = if (x1.n <= x2.n) True else False
}

case object GreaterThan extends ArithmeticComparator{
  def apply(x1: Num, x2: Num): BooleanValue = if (x1.n > x2.n) True else False
}

case object GreaterOrEqualThan extends ArithmeticComparator{
  def apply(x1: Num, x2: Num): BooleanValue = if (x1.n >= x2.n) True else False
}

case class ArithmeticComparison(e1: Expression,
                               e2: Expression,
                               op: ArithmeticComparator
                              ) extends Expression

sealed trait BooleanCombinator {
  def apply(x1: BooleanValue, x2: BooleanValue): BooleanValue
}

case object And extends BooleanCombinator{
  def apply(x1: BooleanValue, x2: BooleanValue): BooleanValue = (x1, x2) match {
    case (False, False) => False
    case (False, True) => False
    case (True, False) => False
    case (True, True) => True
  }
}

case object Or extends BooleanCombinator{
  def apply(x1: BooleanValue, x2: BooleanValue): BooleanValue = (x1, x2) match {
    case (False, False) => False
    case (False, True) => True
    case (True, False) => True
    case (True, True) => True
  }
}

case object Implies extends BooleanCombinator{
  def apply(x1: BooleanValue, x2: BooleanValue): BooleanValue = (x1, x2) match {
    case (False, False) => True
    case (False, True) => True
    case (True, False) => False
    case (True, True) => True
  }
}

case class BooleanCombination(e1: Expression,
                               e2: Expression,
                               op: BooleanCombinator
                              ) extends Expression
