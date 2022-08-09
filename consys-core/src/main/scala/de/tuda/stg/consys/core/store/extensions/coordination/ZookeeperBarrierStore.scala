package de.tuda.stg.consys.core.store.extensions.coordination

import de.tuda.stg.consys.core.store.extensions.{DistributedStore, ZookeeperStore}
import de.tuda.stg.consys.core.store.utils.Address
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.framework.recipes.barriers.DistributedDoubleBarrier
import org.apache.curator.retry.ExponentialBackoffRetry

import java.time.Duration
import java.time.temporal.ChronoUnit
import java.util.concurrent.TimeUnit
import scala.concurrent.duration.{Duration, FiniteDuration}

/**
 * A store that supports barriers.
 */
trait ZookeeperBarrierStore extends ZookeeperStore with BarrierStore {
	protected[store] def curator : CuratorFramework

	/** Enters a barrier with the given name. */
	def barrier(name : String, count : Int, timeout : FiniteDuration) : Unit = {
		val barrier = new DistributedDoubleBarrier(curator, "/consys/barrier/" + name, count)
		barrier.enter(timeout.toMillis, TimeUnit.MILLISECONDS)
		barrier.leave(timeout.toMillis, TimeUnit.MILLISECONDS)
	}

}
