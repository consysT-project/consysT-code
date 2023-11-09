package de.tuda.stg.consys.core.store.akkacluster

import scala.util.DynamicVariable

object AkkaClusterStores {

	private[akkacluster] val currentTransaction : DynamicVariable[AkkaClusterTransactionContext] = new DynamicVariable[AkkaClusterTransactionContext](null)

	def getCurrentTransaction : Option[AkkaClusterTransactionContext] = {
		Option(currentTransaction.value)
	}
}
