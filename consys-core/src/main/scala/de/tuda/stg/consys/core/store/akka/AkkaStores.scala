package de.tuda.stg.consys.core.store.akka

import scala.util.DynamicVariable

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
object AkkaStores {

	private[cassandra] val currentStore : DynamicVariable[AkkaStore] = new DynamicVariable[AkkaStore](null)

	private[cassandra] val currentTransaction : DynamicVariable[AkkaTransactionContext] = new DynamicVariable[AkkaTransactionContext](null)


	def getCurrentStore : Option[AkkaStore] = {
		Option(currentStore.value)
	}

	private[cassandra] def setCurrentStore(tx : AkkaStore) : Unit = currentStore synchronized {
		if (currentStore.value == null) {
			currentStore.value = tx
		} else {
			throw new IllegalStateException(s"unable to set current transaction. transaction already active.\nactive transaction: ${currentTransaction.value}\nnew transaction: $tx")
		}
	}

	def getCurrentTransaction : Option[AkkaTransactionContext] = {
		Option(currentTransaction.value)
	}

	private[cassandra] def setCurrentTransaction(tx : AkkaTransactionContext) : Unit = currentTransaction synchronized {
		if (currentTransaction.value == null) {
			currentTransaction.value = tx
		} else {
			throw new IllegalStateException(s"unable to set current transaction. transaction already active.\nactive transaction: ${currentTransaction.value}\nnew transaction: $tx")
		}
	}

}
