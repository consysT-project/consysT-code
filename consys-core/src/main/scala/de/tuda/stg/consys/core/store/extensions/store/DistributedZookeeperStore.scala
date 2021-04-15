package de.tuda.stg.consys.core.store.extensions.store

import org.apache.curator.framework.CuratorFramework

/**
 * Created on 08.01.20.
 *
 * @author Mirko Köhler
 */
trait DistributedZookeeperStore extends DistributedStore {

	val curator : CuratorFramework
	curator.start()

	override def close() : Unit = {
		super.close()
		curator.close()
	}

}