package de.tudarmstadt.consistency.replobj

import java.util
import java.util.concurrent.{ConcurrentLinkedQueue, TimeUnit}
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.locks.{LockSupport, ReentrantLock}

import akka.actor.{Actor, ActorRef}
import akka.util.Timeout

import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.reflect.api.{TypeCreator, Universe}
import scala.reflect.runtime.universe._



/**
	* Created on 01.03.19.
	*
	* @author Mirko Köhler
	*/
private[replobj] object Utils {

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


	class TxMutexImpl {

		class TxMutexActor extends Actor {

			private val mutex = new TxMutex

			override def receive : Receive = {
				case Lock(txid) =>
					mutex.lockTxid(txid)
					sender ! ()
				case Unlock(txid) =>
					mutex.unlockTxid(txid)
					sender ! ()
				case UnlockAll(txid) =>
					mutex.unlockAllTxid(txid)
					sender ! ()
			}
		}

		case class Lock(txid : Long)
		case class Unlock(txid : Long)
		case class UnlockAll(txid : Long)


		class TxMutexRef private[TxMutexImpl] (private val actorRef : ActorRef) extends Serializable {
			import akka.pattern.ask

			def lock(txid : Long) : Unit =
				Await.result(actorRef.ask(Lock(txid))(timeout = Timeout(180, TimeUnit.SECONDS)), Duration(180, TimeUnit.SECONDS))

			def unlock(txid : Long) : Unit =
				Await.result(actorRef.ask(Unlock(txid))(timeout = Timeout(30, TimeUnit.SECONDS)), Duration(30, TimeUnit.SECONDS))

			def unlockAll(txid : Long) : Unit =
				Await.result(actorRef.ask(UnlockAll(txid))(timeout = Timeout(30, TimeUnit.SECONDS)), Duration(30, TimeUnit.SECONDS))
		}



	}





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


		def unlockTxid(txid : Long) : Unit = {
			lock.lock()

			assert(currentAccessorCount >= 1)
			assert(currentTxid.nonEmpty)
			assert(txid == currentTxid.get)

			currentAccessorCount -= 1

			if (currentAccessorCount == 0) {
				currentTxid = None
				LockSupport.unpark(waiters.peek())
			}

			lock.unlock()
		}

		def unlockAllTxid(txid : Long) : Unit = {
			lock.lock()

			assert(currentAccessorCount >= 1)
			assert(currentTxid.nonEmpty)
			assert(txid == currentTxid.get)

			currentAccessorCount = 0
			currentTxid = None

			LockSupport.unpark(waiters.peek())

			lock.unlock()
		}
	}




//	class FIFOMutex {
//		private val locked : AtomicBoolean = new AtomicBoolean(false)
//		private val waiters : util.Queue[Thread] = new ConcurrentLinkedQueue[Thread]()
//
//		def lock() : Unit = {
//			val current : Thread = Thread.currentThread()
//
//			waiters.add(current)
//
//			// Block while not first in queue or cannot acquire lock
//			var wasInterrupted : Boolean = false
//			while (waiters.peek() != current ||	!locked.compareAndSet(false, true)) {
//				LockSupport.park(this)
//				if (Thread.interrupted()) // ignore interrupts while waiting
//					wasInterrupted = true
//			}
//
//			waiters.remove()
//
//			if (wasInterrupted)          // reassert interrupt status on exit
//				current.interrupt()
//		}
//
//		def unlock() : Unit = {
//			locked.set(false)
//			LockSupport.unpark(waiters.peek())
//		}
//	}

}
