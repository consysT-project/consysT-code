package de.tuda.stg.consys.core.store.extensions.coordination

import com.google.common.collect.Iterables
import de.tuda.stg.consys.core.store.extensions.ETCDStore
import io.etcd.jetcd.options.WatchOption
import io.etcd.jetcd.watch.{WatchEvent, WatchResponse}
import io.etcd.jetcd.{ByteSequence, Client, Watch}

import java.nio.charset.Charset
import java.util.concurrent.{CompletableFuture, CountDownLatch, TimeUnit}
import scala.concurrent.duration.FiniteDuration

trait ETCDBarrierStore extends ETCDStore with BarrierStore {
	protected[store] def etcdClient : Client
	protected[store] def etcdLease : Long

	def barrier(name : String, count : Int, timeout : FiniteDuration) : Unit = synchronized {
		def awaitCompletedValue[T](future : CompletableFuture[T]) = future.get(timeout.toMillis, TimeUnit.MILLISECONDS)
		def byteSequence(str : String) = ByteSequence.from(str, Charset.defaultCharset())

		val counter = byteSequence(s"/consys/barrier/$name/counter")
		val lock = byteSequence(s"/consys/barrier/$name/lock")

		var completed = false
		var watcher : Watch.Watcher = null
		val latch = new CountDownLatch(1)

		val key = etcdClient.getLockClient.lock(lock, etcdLease).get(timeout.toMillis, TimeUnit.MILLISECONDS).getKey
		try {
			val kvs = awaitCompletedValue(etcdClient.getKVClient.get(counter)).getKvs
			if (kvs.size > 1)
				throw new RuntimeException(s"Too many values for barrier key: $counter")
			val number = if (kvs.isEmpty) 1 else kvs.get(0).getValue.toString.toInt

			if (number < count) {
				etcdClient.getKVClient.put(counter, byteSequence((number + 1).toString))
				watcher = etcdClient.getWatchClient.watch(
					counter,
					WatchOption.builder().withRequireLeader(true).withNoPut(true).build(),
					(response : WatchResponse) =>
						if (!response.getEvents.isEmpty && Iterables.getLast(response.getEvents).getEventType == WatchEvent.EventType.DELETE) {
							completed = true
							latch.countDown()
						},
					(_: Throwable) => latch.countDown(),
					() => latch.countDown())
			}
			else {
				completed = true
				latch.countDown()
				etcdClient.getKVClient.delete(counter)
			}
		}
		finally {
			etcdClient.getLockClient.unlock(key)
		}

		latch.await(timeout.toMillis, TimeUnit.MILLISECONDS)

		if (watcher != null)
			watcher.close()

		if (!completed)
			throw new RuntimeException(s"Exited barrier unexpectedly.")
	}
}
