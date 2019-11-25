package de.tuda.stg.consys.objects

import scala.concurrent.duration.Duration

/**
	* Provides functionality for thze current thread to check and modify his transaction status.
	*
	* @author Mirko Köhler
	*/
trait BarrierReplicaSystem extends ReplicaSystem {

	def barrier(name : String, timeout : Duration) : Unit

}
