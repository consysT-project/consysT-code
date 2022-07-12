package de.tuda.stg.consys.core.store.extensions.store

import de.tuda.stg.consys.core.store.extensions.store.DistributedZookeeperLockingStore.ZookeeperLock
import de.tuda.stg.consys.core.store.extensions.store.LockingStore.DistributedLock
import java.util.concurrent.{TimeUnit, TimeoutException}
import org.apache.curator.framework.recipes.locks.{InterProcessLock, InterProcessMutex}

/**
 * Created on 08.01.20.
 *
 * @author Mirko Köhler
 */
trait DistributedZookeeperLockingStore extends DistributedZookeeperStore with LockingStore {

	override type LockType = ZookeeperLock

	//Create path for locks
	curator.create().orSetData().forPath("/consys")
	curator.create().orSetData().forPath("/consys/locks")

	override def lockFor(addr : Addr) : LockType = {
		val processLock = new InterProcessMutex(curator, s"/consys/locks/$addr")
		new ZookeeperLock(this, processLock)
	}

	override def close() : Unit = {
		super.close()
	}

}

object DistributedZookeeperLockingStore {

	class ZookeeperLock(store : DistributedStore, lock : InterProcessLock) extends DistributedLock {
		override def acquire() : Unit = {
			if (!lock.acquire(store.timeout.toMillis, TimeUnit.MILLISECONDS)) {
				throw new TimeoutException(s"timeout during acquiring the lock for $lock")
			}
		}
		override def release() : Unit = {
			lock.release()
		}
	}
}


