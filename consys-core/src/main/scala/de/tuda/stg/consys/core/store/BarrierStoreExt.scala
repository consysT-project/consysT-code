package de.tuda.stg.consys.core.store

import scala.concurrent.duration.Duration

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait BarrierStoreExt { self : DistributedStore =>

	def barrier(name : String, timeout : Duration = timeout) : Unit


}
