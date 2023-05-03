package de.tuda.consys.invariants.solver.next

import com.microsoft.z3.Sort
import de.tuda.consys.invariants.solver.next.ir.IR.Type

package object translate {

	type TypeMap = Map[Type, TypeRep]

	def findRepInTypeMap(typeMap : TypeMap, sort : Sort) : Option[TypeRep] = {
		typeMap.find(t => t._2.sort == sort).map(t => t._2)
	}


}
