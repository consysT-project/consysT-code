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
class TxMutex {

	private val sync : Sync = new Sync

	def lockFor(txid : Long) : Unit = sync.acquire(txid)
	def unlockFor(txid : Long) : Unit = sync.release(txid)

	def assertTx(txid : Long) : Unit =
		assert(sync.isAcquiredBy(txid))
}


object TxMutex extends Serializable {


	def main(args : Array[String]) : Unit = {
		val mutex = new TxMutex


		implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(8))


		def f(txid : Long) : Unit = Future {
			println(s"Try $txid...")
			mutex.lockFor(txid)
			println(s"Start $txid...")

			Await.ready(Future {
				mutex.assertTx(txid)
				println(txid)
				Thread.sleep(100)
				mutex.assertTx(txid)
				println(txid)
				Thread.sleep(100)
			}, 30 seconds)

			println(s"Finish $txid...")
			mutex.unlockFor(txid)
		}

		f(100)
		f(200)
		f(300)

		Thread.sleep(5000)

	}




	private class Sync extends AbstractQueuedLongSynchronizer {
		setState(-1)

		// Reports whether in locked state
		override protected def isHeldExclusively : Boolean = getState != -1

		// Acquires the lock if state is zero
		override def tryAcquire(acquires : Long) : Boolean = {

			if (compareAndSetState(-1, acquires)) {
				setExclusiveOwnerThread(Thread.currentThread)
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

		// Deserializes properly
//		@throws[IOException]
//		@throws[ClassNotFoundException]
//		private def readObject(s : ObjectInputStream) : Unit = {
//			s.defaultReadObject()
//			setState(0) // reset to unlocked state
//
//		}
	}









}