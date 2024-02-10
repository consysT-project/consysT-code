package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.Store
import org.apache.curator.framework.CuratorFramework

/**
 * A store that supports barriers.
 */
trait ZookeeperStore extends Store {
	protected[store] def curator : CuratorFramework


}
