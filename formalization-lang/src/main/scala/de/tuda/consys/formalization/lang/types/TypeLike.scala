package de.tuda.consys.formalization.lang.types

trait TypeLike[A] {
    def <=(t: A): Boolean

    def !<=(t: A): Boolean = !this.<=(t)

    def >=(t: A): Boolean

    def !>=(t: A): Boolean = !this.>=(t)

    def lub(t: A): A

    def glb(t: A): A
}