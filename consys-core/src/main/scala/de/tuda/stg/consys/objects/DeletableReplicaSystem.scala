package de.tuda.stg.consys.objects

import scala.language.higherKinds
import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait DeletableReplicaSystem extends ReplicaSystem {

	def delete(addr : Addr) : Unit

	def clear(except : Set[Addr] = Set.empty) : Unit

}
