package de.tuda.stg.consys.core.store.cassandra

import java.util.concurrent.{TimeUnit, TimeoutException}

import de.tuda.stg.consys.core.store.DistributedStore
import de.tuda.stg.consys.core.store.cassandra.LockingStoreExt.ZookeeperLock
import org.apache.curator.framework.CuratorFramework
import org.apache.curator.framework.recipes.locks.InterProcessMutex

/**
 * Created on 08.01.20.
 *
 * @author Mirko Köhler
 */
trait LockingStoreExt { self : DistributedStore with ZookeeperStoreExt =>

	//Create path for locks
	curator.create().orSetData().forPath("/consys")
	curator.create().orSetData().forPath("/consys/locks")

	def lockFor(addr : Addr) : ZookeeperLock = new ZookeeperLock {
		val lock = new InterProcessMutex(curator, s"/consys/locks/$addr")

		override def acquire() : Unit = {
			if (!lock.acquire(timeout.toMillis, TimeUnit.MILLISECONDS)) {
				throw new TimeoutException(s"timeout during acquiring the lock for $addr")
			}
		}

		override def release() : Unit = {
			lock.release()
		}
	}

	override def close() : Unit = {
		curator.close()
	}

}

object LockingStoreExt {

	trait ZookeeperLock {
		def acquire() : Unit
		def release() : Unit
	}

}


