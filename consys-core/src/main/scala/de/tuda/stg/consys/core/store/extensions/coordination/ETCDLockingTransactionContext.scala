package de.tuda.stg.consys.core.store.extensions.coordination

import de.tuda.stg.consys.core.store.extensions.{DistributedStore, ETCDStore}
import io.etcd.jetcd.ByteSequence

import java.nio.charset.Charset
import java.util.concurrent.TimeUnit

trait ETCDLockingTransactionContext[StoreType <: ETCDStore with DistributedStore] extends LockingTransactionContext[StoreType] {
	override protected def createLockFor(addr : StoreType#Addr) = new DistributedLock {
		private val name = ByteSequence.from(s"/consys/locks/$addr", Charset.defaultCharset())
		private var key : ByteSequence = null

		override def acquire() = synchronized {
			if (key == null)
				key = store.etcdClient.getLockClient.lock(name, store.etcdLease).get(store.timeout.toMillis, TimeUnit.MILLISECONDS).getKey
		}

		override def release() = synchronized {
			if (key != null) {
				store.etcdClient.getLockClient.unlock(key)
				key = null
			}
		}
	}
}
