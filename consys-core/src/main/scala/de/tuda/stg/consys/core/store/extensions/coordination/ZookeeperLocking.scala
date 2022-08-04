package de.tuda.stg.consys.core.store.extensions.coordination

import akka.util.Timeout
import org.apache.curator.framework.CuratorFramework
import org.apache.curator.framework.recipes.locks.{InterProcessLock, InterProcessMutex}

import java.util.concurrent.{TimeUnit, TimeoutException}

class ZookeeperLocking[Addr](val curator : CuratorFramework) {

	curator.start()
	curator.blockUntilConnected()

	//Create path for locks
	curator.create().orSetData().forPath("/consys")
	curator.create().orSetData().forPath("/consys/locks")

	def createLockFor(addr : Addr, timeout : Timeout) : DistributedLock = {
		val processLock = new InterProcessMutex(curator, s"/consys/locks/$addr")
		new ZookeeperLock(processLock, timeout)
	}


	def close() : Unit = {
		curator.close()
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
