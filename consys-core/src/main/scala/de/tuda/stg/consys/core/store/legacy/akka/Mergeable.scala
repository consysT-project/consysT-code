package de.tuda.stg.consys.core.store.legacy.akka

trait Mergeable[T]{
  private[akka] def merge(other:T)

}
