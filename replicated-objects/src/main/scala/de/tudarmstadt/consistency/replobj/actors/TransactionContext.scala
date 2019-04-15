package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ConsistencyLevel
import de.tudarmstadt.consistency.replobj.actors.Transaction.ToplevelTransaction

import scala.util.Random

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
class TransactionContext {

	private var currentTransaction : Transaction = null


//	private val builder : DynamicVariable[Option[ContextPathBuilder]] = new DynamicVariable(None)
//	val locked : DynamicVariable[mutable.Buffer[LockableReplicatedObject[_]]] = new DynamicVariable(mutable.Buffer.empty)

	/**
		* Checks whether there is an active transaction on the
		* @return
		*/
	def hasCurrentTransaction : Boolean =
		currentTransaction != null

	def getCurrentTransaction : Transaction = {
		require(hasCurrentTransaction)
		currentTransaction
	}

	def isNested : Boolean = {
		!getCurrentTransaction.isToplevel
	}


	def newTransaction(consistencyLevel : ConsistencyLevel) : Unit = {
		if (hasCurrentTransaction) {
			currentTransaction = currentTransaction.start(consistencyLevel)
		} else {
			currentTransaction = new ToplevelTransaction(Random.nextLong, consistencyLevel)
		}
		println(Thread.currentThread() + " new tx " + currentTransaction)
	}

	def commitTransaction() : Unit = {
		println(Thread.currentThread() + " commit tx " + currentTransaction)

		if (!hasCurrentTransaction) {
			assert(false, "thread: " + Thread.currentThread())
		}

		require(hasCurrentTransaction)

		currentTransaction.getParent match {
			case None => currentTransaction = null
			case Some(tx) => currentTransaction = tx
		}
	}

	def setCurrentTransaction(tx : Transaction) : Unit = {
		require(!hasCurrentTransaction)
		currentTransaction = tx
	}

	/**
		* Clears the current state of the transaction and resets it to fresh
		*/
	def clear() : Unit = {
		println(Thread.currentThread() + " clear tx " + currentTransaction)
		currentTransaction = null
	}



	override def toString : String = s"TransactionContext($currentTransaction)"

}
