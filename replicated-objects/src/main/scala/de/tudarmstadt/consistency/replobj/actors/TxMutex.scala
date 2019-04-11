package de.tudarmstadt.consistency.replobj.actors

import java.util
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.locks.{LockSupport, ReentrantLock}

import scala.language.postfixOps

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/


//Implementation adapted from https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/locks/LockSupport.html
class TxMutex {

	//Lock for accessing this objects data structures.
	private val lock = new ReentrantLock()

	private var currentTxid : Option[Long] = None
	private var currentAccessorCount = 0
	private val waiters : util.Queue[Thread] = new ConcurrentLinkedQueue[Thread]()


	def compareAndSet(txid : Long) : Boolean = currentTxid match {
		case Some(x) if x == txid =>
			true
		case Some(_) => false
		case None =>
			currentTxid = Some(txid)
			true
	}


	def lockTxid(txid : Long) : Unit = {
		val currentThread : Thread = Thread.currentThread()

		waiters.add(currentThread)
		var wasInterrupted : Boolean = false

		lock.lock()
		while (!compareAndSet(txid)) {
			lock.unlock()
			LockSupport.park(this)

			if (Thread.interrupted())
				wasInterrupted = true

			lock.lock()
		}

		waiters.remove(currentThread)
		currentAccessorCount += 1
		lock.unlock()

		if (wasInterrupted) currentThread.interrupt()
	}


	def unlockTxid() : Unit = {
		lock.lock()

		assert(currentAccessorCount >= 1)
		assert(currentTxid.nonEmpty)

		currentAccessorCount -= 1

		if (currentAccessorCount == 0) {
			currentTxid = None
			LockSupport.unpark(waiters.peek())
		}

		lock.unlock()
	}
}




class FIFOMutex {
	private val locked : AtomicBoolean = new AtomicBoolean(false)
	private val waiters : util.Queue[Thread] = new ConcurrentLinkedQueue[Thread]()

	def lock() : Unit = {
		val current : Thread = Thread.currentThread()

		waiters.add(current)

		// Block while not first in queue or cannot acquire lock
		var wasInterrupted : Boolean = false
		while (waiters.peek() != current ||	!locked.compareAndSet(false, true)) {
			LockSupport.park(this)
			if (Thread.interrupted()) // ignore interrupts while waiting
				wasInterrupted = true
		}

		waiters.remove()

		if (wasInterrupted)          // reassert interrupt status on exit
			current.interrupt()
	}

	def unlock() : Unit = {
		locked.set(false)
		LockSupport.unpark(waiters.peek())
	}
}
