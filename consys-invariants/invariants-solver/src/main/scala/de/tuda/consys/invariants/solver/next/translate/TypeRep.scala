package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{FuncDecl, Sort, TupleSort}
import de.tuda.consys.invariants.solver.next.ir.IR.{FieldId, IRType, MethodId}

trait TypeRep {
	def sort : Sort
}

object TypeRep {

	case class ObjectTypeRep(
		override val sort : TupleSort,
		accessors : Map[FieldId, FuncDecl[_]],
		methods : Map[(MethodId, Seq[IRType]), FuncDecl[_]]
	) extends TypeRep

	case class NativeTypeRep(override val sort : Sort) extends TypeRep
}
