package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.DistributedStore
import org.apache.curator.framework.CuratorFramework

/**
 * Created on 08.01.20.
 *
 * @author Mirko Köhler
 */
trait ZookeeperStoreExt { self : DistributedStore =>

	val curator : CuratorFramework
	curator.start()

		override def close() : Unit = {
		curator.close()
	}

}