package de.tudarmstadt.consistency.store.objects

import scala.language.implicitConversions

/**
	* Created on 21.11.18.
	*
	* @author Mirko Köhler
	*/
trait ConsistencyLattice[Consistency] {

	def top : Consistency
	def bot : Consistency

	def intersect(c1 : Consistency, c2 : Consistency) : Consistency
	def union(c1 : Consistency, c2 : Consistency) : Consistency

	def smallerEq(c1 : Consistency, c2 : Consistency) : Boolean

	class ConsistencyOps(c1 : Consistency) {
		def <(c2 : Consistency) : Boolean = smallerEq(c1, c2)
		def cup(c2 : Consistency) : Consistency = union(c1, c2)
		def cap(c2 : Consistency) : Consistency = intersect(c1, c2)
	}

	implicit def consistencyToOps(c1 : Consistency) : ConsistencyOps =
		new ConsistencyOps(c1)

}
