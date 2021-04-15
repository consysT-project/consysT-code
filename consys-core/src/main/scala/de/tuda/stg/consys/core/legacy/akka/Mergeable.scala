package de.tuda.stg.consys.core.legacy.akka

trait Mergeable[T]{
  private[akka] def merge(other:T)

}
