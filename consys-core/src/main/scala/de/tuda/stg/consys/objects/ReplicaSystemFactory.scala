package de.tuda.stg.consys.objects

/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
trait ReplicaSystemFactory {

	type System <: ReplicaSystem

	def create(host : Address, others : Seq[Address])

}
