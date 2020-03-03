package de.tuda.stg.consys.core.store.akka

import scala.util.DynamicVariable

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
object AkkaStores {

	private[akka] val currentStore : DynamicVariable[AkkaStore] = new DynamicVariable[AkkaStore](null)

	private[akka] val currentTransaction : DynamicVariable[AkkaTransactionContext] = new DynamicVariable[AkkaTransactionContext](null)


	def getCurrentStore : Option[AkkaStore] = {
		Option(currentStore.value)
	}

	private[akka] def setCurrentStore(store : AkkaStore) : Unit =
		if (currentStore.value == null) {
			currentStore.value = store
		} else {
			throw new IllegalStateException(s"unable to set current store. store already active.\nactive store: ${currentStore.value}\nnew store: $store")
		}


	def getCurrentTransaction : Option[AkkaTransactionContext] = {
		Option(currentTransaction.value)
	}

	private[akka] def setCurrentTransaction(tx : AkkaTransactionContext) : Unit =
		if (currentTransaction.value == null) {
			currentTransaction.value = tx
		} else {
			throw new IllegalStateException(s"unable to set current transaction. transaction already active.\nactive transaction: ${currentTransaction.value}\nnew transaction: $tx")
		}


}
