package de.tuda.stg.consys.core.store.extensions.coordination

import akka.util.Timeout
import de.tuda.stg.consys.core.store.extensions.{DistributedStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.{Store, TransactionContext}
import org.apache.curator.framework.recipes.locks.{InterProcessLock, InterProcessMutex}

import java.util.concurrent.{TimeUnit, TimeoutException}
import scala.collection.mutable

/**
 * Created on 16.01.20.
 *
 * @author Mirko Köhler
 */
trait ZookeeperLockingTransactionContext[StoreType <: ZookeeperStore with DistributedStore] extends LockingTransactionContext[StoreType] {

	override protected def createLockFor(addr : StoreType#Addr) : DistributedLock = {
		val processLock = new InterProcessMutex(store.curator, s"/consys/locks/$addr")

		new ZookeeperLock(processLock, store.timeout)
	}


	private class ZookeeperLock(lock : InterProcessLock, timeout : Timeout) extends DistributedLock {
		override def acquire() : Unit = {
			if (!lock.acquire(timeout.duration.toMillis, TimeUnit.MILLISECONDS)) {
				throw new TimeoutException(s"timeout during acquiring the lock for $lock")
			}
		}
		override def release() : Unit = {
			lock.release()
		}
	}


}

