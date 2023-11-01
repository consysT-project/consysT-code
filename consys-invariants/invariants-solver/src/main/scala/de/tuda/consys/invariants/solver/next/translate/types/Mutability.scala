package de.tuda.consys.invariants.solver.next.translate.types

object Mutability {

  trait M {
    def union(other : M) : M
  }

  case object Immutable extends M {
    override def union(other : M) : M = other
  }

  case object Mutable extends M {
    override def union(other : M) : M = Mutable
  }

}
