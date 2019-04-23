package de.tuda.stg.consys.objects

/**
	* Created on 16.04.19.
	*
	* @author Mirko Köhler
	*/
trait LockServiceReplicaSystem[Addr, Tx] extends ReplicaSystem[Addr] {


	def acquireLock(addr : Addr, tx : Tx) : Unit
		/*Override this for performance enhancements*/
//		lockAndRetrieveState(addr, tx)

//	def lockAndRetrieveState[T <: AnyRef](addr : Addr, tx : Tx) : T

	def releaseLock(addr : Addr, tx : Tx) : Unit

}
