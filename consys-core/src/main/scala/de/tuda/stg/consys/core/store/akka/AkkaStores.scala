package de.tuda.stg.consys.core.store.akka

import scala.util.DynamicVariable

object AkkaStores {

	private[akka] val currentTransaction : DynamicVariable[AkkaTransactionContext] = new DynamicVariable[AkkaTransactionContext](null)

	def getCurrentTransaction : Option[AkkaTransactionContext] = {
		Option(currentTransaction.value)
	}
}
