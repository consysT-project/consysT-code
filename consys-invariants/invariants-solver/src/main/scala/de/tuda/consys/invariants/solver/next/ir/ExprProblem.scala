package de.tuda.consys.invariants.solver.next.ir

trait Base {
  type exp <: Exp

  trait Exp {
    def eval: Int
  }


  class Num(val value: Int) extends Exp {
    def eval: Int = value
  }

  type BaseNum = Num
}

trait BasePlus extends Base {

  class Plus(val left: exp, val right: exp) extends Exp {
    def eval: Int = left.eval + right.eval
  }

  type BasePlus = Plus
}

trait BaseNeg extends Base {

  class Neg(val term: exp) extends Exp {
    def eval = -term.eval
  }

  type BaseNeg = Neg
}

trait BasePlusNeg extends BasePlus with BaseNeg

trait Show extends Base {
  type exp <: Exp

  trait Exp extends super.Exp {
    def show: String
  }

  trait NumBehavior extends Exp {
    self: BaseNum =>
    override def show: String = value.toString
  }

  final class Num(v: Int) extends BaseNum(v) with NumBehavior with Exp

}

trait ShowPlusNeg extends BasePlusNeg with Show {

  trait PlusBehavior {
    self: BasePlus =>
    def show = left.show + "+" + right.show;
  }

  final class Plus(l: exp, r: exp) extends BasePlus(l, r) with PlusBehavior with Exp

  trait NegBehavior {
    self: BaseNeg =>
    def show = "-(" + term.show + ")";
  }

  class Neg(t: exp) extends BaseNeg(t) with NegBehavior with Exp

}

trait DblePlusNeg extends BasePlusNeg {
  type exp <: Exp

  trait Exp extends super.Exp {
    def dble: exp
  }

  def Num(v: Int): exp

  def Plus(l: exp, r: exp): exp

  def Neg(t: exp): exp


  trait NumBehavior {
    self: BaseNum =>
    def dble = Num(value * 2)
  }

  final class Num(v: Int) extends BaseNum(v) with NumBehavior with Exp


  trait PlusBehavior {
    self: BasePlus =>
    def dble = Plus(left.dble, right.dble)
  }

  class Plus(l: exp, r: exp) extends BasePlus(l, r) with PlusBehavior with Exp


  trait NegBehavior {
    self: BaseNeg =>
    def dble = Neg(term.dble)
  }

  class Neg(t: exp) extends super.Neg(t) with NegBehavior with Exp

}

trait ShowDblePlusNeg extends ShowPlusNeg with DblePlusNeg {
  type exp <: Exp

  trait Exp extends super[ShowPlusNeg].Exp with super[DblePlusNeg].Exp;

  trait NumBehavior extends super[ShowPlusNeg].NumBehavior with super[DblePlusNeg].NumBehavior {
    self: BaseNum =>
  }

  final class Num(v: Int) extends BaseNum(v)
    with NumBehavior
    with Exp


  trait PlusBehavior extends super[ShowPlusNeg].PlusBehavior with super[DblePlusNeg].PlusBehavior {
    self: BasePlus =>
  }

  final class Plus(l: exp, r: exp) extends BasePlus(l, r)
    with PlusBehavior
    with Exp

  trait NegBehavior extends super[ShowPlusNeg].NegBehavior with super[DblePlusNeg].NegBehavior {
    self: BaseNeg =>
  }

  final class Neg(t: exp) extends BaseNeg(t)
    with NegBehavior
    with Exp

}

trait Equals extends Base {
  type exp <: Exp;

  trait Exp extends super.Exp {
    def eql(other: exp): Boolean;

    def isNum(v: Int): Boolean = false;
  }

  trait NumBehavior extends Exp {
    self: BaseNum =>
    def eql(other: exp): Boolean = other.isNum(value);

    override def isNum(v: Int) = v == value;
  }


  final class Num(v: Int) extends BaseNum(v) with NumBehavior with Exp

}

trait EqualsPlusNeg extends BasePlusNeg with Equals {
  type exp <: Exp;

  trait Exp extends super[BasePlusNeg].Exp
    with super[Equals].Exp {
    def isPlus(l: exp, r: exp): Boolean = false;

    def isNeg(t: exp): Boolean = false;
  }


  final class Num(v: Int) extends BaseNum(v)
    with NumBehavior // effectively super[Equals].NumBehavior
    with Exp


  trait PlusBehavior extends Exp {
    self: BasePlus =>
    def eql(other: exp): Boolean = other.isPlus(left, right);

    override def isPlus(l: exp, r: exp) = (left eql l) && (right eql r)
  }

  final class Plus(l: exp, r: exp) extends BasePlus(l, r) with PlusBehavior with Exp


  trait NegBehavior extends Exp {
    self: BaseNeg =>
    def eql(other: exp): Boolean = other.isNeg(term);

    override def isNeg(t: exp) = term eql t
  }

  final class Neg(t: exp) extends BaseNeg(t) with NegBehavior with Exp

}

trait EqualsShowPlusNeg extends EqualsPlusNeg with ShowPlusNeg {
  type exp <: Exp

  trait Exp extends super[EqualsPlusNeg].Exp
    with super[ShowPlusNeg].Exp


  trait NumBehavior extends super[EqualsPlusNeg].NumBehavior with super[ShowPlusNeg].NumBehavior {
    self: BaseNum =>
  }

  class Num(v: Int) extends BaseNum(v) with NumBehavior with Exp

  trait PlusBehavior extends super[EqualsPlusNeg].PlusBehavior with super[ShowPlusNeg].PlusBehavior {
    self: BasePlus =>
  }

  class Plus(l: exp, r: exp) extends BasePlus(l, r) with PlusBehavior with Exp

  trait NegBehavior extends super[EqualsPlusNeg].NegBehavior with super[ShowPlusNeg].NegBehavior {
    self: BaseNeg =>
  }

  class Neg(term: exp) extends BaseNeg(term) with NegBehavior with Exp

}