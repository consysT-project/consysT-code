package de.tuda.stg.consys.core.store.akkacluster.backend

import akka.cluster.ddata.ReplicatedData
import de.tuda.stg.consys.Mergeable

class MergeableReplicatedData[A <: Mergeable[A]](
	val mergeable : A
) extends ReplicatedData {
	override type T = this.type

	override def merge(that : this.type) : this.type = {
		mergeable.merge(that.mergeable)
		this
	}
}
