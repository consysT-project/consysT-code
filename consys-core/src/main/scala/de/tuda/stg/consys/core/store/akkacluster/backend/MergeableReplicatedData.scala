package de.tuda.stg.consys.core.store.akkacluster.backend

import akka.cluster.ddata.ReplicatedData
import de.tuda.stg.consys.Mergeable

case class MergeableReplicatedData[A](
	mergeable : Mergeable[A]
) extends ReplicatedData {

	override type T = MergeableReplicatedData[A]

	override def merge(that : T) : T = {
		mergeable.merge(that.mergeable.asInstanceOf[A])
		this
	}
}
