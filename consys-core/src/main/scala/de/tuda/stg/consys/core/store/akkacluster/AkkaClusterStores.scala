package de.tuda.stg.consys.core.store.akkacluster

import scala.util.DynamicVariable

object AkkaClusterStores {

	private[akkacluster] val currentTransaction : DynamicVariable[AkkaClusterStore#TxContext] = new DynamicVariable[AkkaClusterStore#TxContext](null)

	def getCurrentTransaction : Option[AkkaClusterStore#TxContext] = {
		Option(currentTransaction.value)
	}
}
