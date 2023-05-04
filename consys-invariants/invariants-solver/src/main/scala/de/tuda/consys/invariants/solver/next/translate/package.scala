package de.tuda.consys.invariants.solver.next

import com.microsoft.z3.Sort
import de.tuda.consys.invariants.solver.next.ir.IR.{ClassId, Type}
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.ClassRep

package object translate {

	type RepTable = Map[ClassId, ClassRep]

	def sortToClassRep(repTable : RepTable, sort : Sort) : Option[(ClassId, ClassRep)] = {
		repTable.find(t => t._2.sort == sort)
	}


}
