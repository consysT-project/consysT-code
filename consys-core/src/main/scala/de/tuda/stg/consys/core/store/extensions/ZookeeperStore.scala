package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.Store
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry

/**
 * A store that supports barriers.
 */
trait ZookeeperStore extends Store {
	protected[store] def curator : CuratorFramework
}

object ZookeeperStore {
	def createCurator(host : String, port : Int) : CuratorFramework = {
		val curator = CuratorFrameworkFactory.newClient(s"$host:$port", new ExponentialBackoffRetry(250, 3))
		curator.start()
		curator.blockUntilConnected()
		curator
	}
}
