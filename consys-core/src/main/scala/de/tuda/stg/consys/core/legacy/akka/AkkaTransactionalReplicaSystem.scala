package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.{ConsistencyLabel, TransactionalReplicaSystem}
import scala.util.DynamicVariable

/**
	* Created on 16.04.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaTransactionalReplicaSystem extends TransactionalReplicaSystem {

	override type Tx = Transaction

	private val threadContext : DynamicVariable[TransactionContext] = new DynamicVariable(null)

	private def context : TransactionContext = {
		if (threadContext.value == null)
			threadContext.value = new TransactionContext

		threadContext.value
	}

	override def clearTransaction() : Unit = {
		if (threadContext.value != null) {
			threadContext.value.clear()
			threadContext.value = null
		}
	}

	override def hasCurrentTransaction : Boolean = context.hasCurrentTransaction

	override def getCurrentTransaction : Tx = context.getCurrentTransaction

	override def newTransaction(consistencyLevel : ConsistencyLevel) : Unit =
		context.newTransaction(consistencyLevel.asInstanceOf[ConsistencyLabel])

	override def commitTransaction() : Unit =
		context.commitTransaction()

	override def setCurrentTransaction(tx : Tx) : Unit =
		context.setCurrentTransaction(tx)
}
