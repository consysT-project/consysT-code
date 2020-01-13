package de.tuda.stg.consys.core.store

import scala.concurrent.duration.FiniteDuration

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
trait DistributedStore extends Store {
	def timeout : FiniteDuration
}
