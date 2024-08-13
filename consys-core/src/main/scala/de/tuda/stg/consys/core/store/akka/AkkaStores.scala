package de.tuda.stg.consys.core.store.akka

import scala.util.DynamicVariable

object AkkaStores {

	private[akka] val currentTransaction : DynamicVariable[AkkaStore#TxContext] =
		new DynamicVariable[AkkaStore#TxContext](null)

	def getCurrentTransaction : Option[AkkaStore#TxContext] = {
		Option(currentTransaction.value)
	}
}
