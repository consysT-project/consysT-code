package de.tuda.stg.consys.core.legacy

import java.util
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.locks.{LockSupport, ReentrantLock}
import scala.reflect.ClassTag
import scala.reflect.api.{TypeCreator, Universe}
import scala.reflect.runtime.universe._

/**
	* Created on 01.03.19.
	*
	* @author Mirko Köhler
	*/
private[consys] object ConsysUtils {

	def typeTagFromCls[T](cls : Class[T]) : TypeTag[T] = {
		/*TODO: Is there a better way to obtain TypeTags in Java code? These type tags here are not serializable.*/
		val mirror : Mirror = runtimeMirror(cls.getClassLoader)
		val tpe = mirror.classSymbol(cls).toType

		val objTypeCreator = SimpleTypeCreator(mirror, tpe)

		TypeTag[T](mirror, objTypeCreator)
	}

	private case class SimpleTypeCreator(mirror : Mirror, tpe : Type) extends TypeCreator {
		override def apply[U <: Universe with Singleton](m1: scala.reflect.api.Mirror[U]): U#Type =
			if (m1 != mirror)
				sys.error("wrong mirror")
			else
				tpe.asInstanceOf[U#Type]
	}

	def typeToClassTag[T: TypeTag]: ClassTag[T] =
		ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )


	def classToClassTag[T](clazz : Class[T]) : ClassTag[T] = {
		val rtMirror = runtimeMirror(clazz.getClassLoader)
		ClassTag[T](rtMirror.runtimeClass(rtMirror.classSymbol(clazz).toType))
	}


	/*Implementation adapted from https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/locks/LockSupport.html:
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
		}*/
	class TxMutex {
		//Lock for accessing this objects data structures.
		//Can never be locked for a long time!
		private val mutexLock = new ReentrantLock()

		private var currentTxid : Option[Long] = None
		private var currentAccessorCount = 0
		private val waiters : util.Queue[Thread] = new ConcurrentLinkedQueue[Thread]()

		def unsafeCurrentTxid : Option[Long] = currentTxid

		def compareAndSet(txid : Long) : Boolean = currentTxid match {
			case Some(x) if x == txid =>
				true
			case Some(_) => false
			case None =>
				currentTxid = Some(txid)
				true
		}

		def tryLockTxid(txid : Long) : Boolean = {
			mutexLock.lock() //Request to access the locks data structures.
		  val result = compareAndSet(txid)
			if (result) currentAccessorCount += 1
			mutexLock.unlock()

			result
		}

		def lockTxid(txid : Long) : Unit = {
			val currentThread : Thread = Thread.currentThread()

			waiters.add(currentThread)
			var wasInterrupted : Boolean = false

			mutexLock.lock()
			while (!compareAndSet(txid)) {
				mutexLock.unlock()
				LockSupport.park(this)

				if (Thread.interrupted())
					wasInterrupted = true

				mutexLock.lock()
			}

			waiters.remove(currentThread)
			currentAccessorCount += 1
			mutexLock.unlock()

			if (wasInterrupted) currentThread.interrupt()
		}


		def unlockTxid(txid : Long) : Unit = {
			mutexLock.lock()

			assert(currentAccessorCount >= 1)
			assert(currentTxid.nonEmpty)
			assert(txid == currentTxid.get)

			currentAccessorCount -= 1

			if (currentAccessorCount == 0) {
				currentTxid = None
				LockSupport.unpark(waiters.peek()) //if waiters is empty, then peek is null and unpark(null) is a nop
			}

			mutexLock.unlock()
		}

		def unlockAllTxid(txid : Long) : Unit = {
			mutexLock.lock()

//			if (currentAccessorCount == 0 && currentTxid.isEmpty)
//				return

			assert(currentAccessorCount >= 1)
			assert(currentTxid.nonEmpty)
			assert(txid == currentTxid.get)

			currentAccessorCount = 0
			currentTxid = None

			LockSupport.unpark(waiters.peek())

			mutexLock.unlock()
		}
	}



}
