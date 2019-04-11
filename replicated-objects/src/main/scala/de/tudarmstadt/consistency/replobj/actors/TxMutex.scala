package de.tudarmstadt.consistency.replobj.actors

import java.util.concurrent.{Callable, ExecutorService, Executors}
import java.util.concurrent.locks.{AbstractQueuedLongSynchronizer, AbstractQueuedSynchronizer}

import de.tudarmstadt.consistency.replobj.actors.TxMutex.Sync

import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutor, Future}
import scala.concurrent.duration._
import scala.language.postfixOps

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/
class TxMutex extends Serializable {

	private val sync : Sync = new Sync

	def lockFor(txid : Long) : Unit = sync.acquire(txid)
	def unlockFor(txid : Long) : Unit = sync.release(txid)

	def assertTx(txid : Long) : Unit =
		assert(sync.isAcquiredBy(txid))
}


object TxMutex {



	private class Sync extends AbstractQueuedLongSynchronizer {
		setState(-1)

		// Reports whether in locked state
		override protected def isHeldExclusively : Boolean = getState != -1

		// Acquires the lock if state is zero
		override def tryAcquire(acquires : Long) : Boolean = {

			if (compareAndSetState(-1, acquires)) {
				setExclusiveOwnerThread(Thread.currentThread)
				return true
			} else if (getState == acquires) {
				return true
			}
			false
		}

		// Releases the lock by setting state to zero
		override protected def tryRelease(releases : Long) : Boolean = {
			val state = getState

			if (getState == -1 || getState != releases)
				throw new IllegalMonitorStateException

			setExclusiveOwnerThread(null)
			setState(-1)
			true
		}

		def isAcquiredBy(txid : Long) : Boolean =	getState == txid

		// Provides a Condition
		def newCondition = new ConditionObject


	}









}