package de.tuda.consys.formalization.lang.types

class LatticeNode[T](value: T, parents: => List[LatticeNode[T]], children: => List[LatticeNode[T]]) {
    def hasUpperBound(t: T): Boolean = t match {
        case `value` => true
        case _ => parents.exists(p => p.hasUpperBound(t))
    }

    def hasLowerBound(t: T): Boolean = t match {
        case `value` => true
        case _ => children.exists(p => p.hasLowerBound(t))
    }
}
