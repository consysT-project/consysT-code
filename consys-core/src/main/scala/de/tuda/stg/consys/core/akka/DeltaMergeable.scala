package de.tuda.stg.consys.core.akka

/**
 * Classes with this trait allow being updated with a delta state
 * @tparam T delta state type
 */
trait DeltaMergeable {

  private[akka] def merge(other:AkkaReplicaSystem#Obj)

}


