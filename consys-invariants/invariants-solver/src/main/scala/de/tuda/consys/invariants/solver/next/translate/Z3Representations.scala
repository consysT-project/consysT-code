package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, FuncDecl, Sort, TupleSort}
import de.tuda.consys.invariants.solver.next.ir.IR.{FieldId, MethodId, Type, TypeVarId}


object Z3Representations {

	trait ClassRep {
		def sortFactory : Seq[Sort] => Sort
		def typeParameters : Map[TypeVarId, Sort]
		def methods : Map[MethodId, MethodRep]

		def getField(fieldId : FieldId) : Option[FieldRep]
		def getMethod(methodId : MethodId) : Option[MethodRep]
	}

	case class ObjectClassRep(
		 sort : TupleSort,
		 fields : Map[FieldId, FieldRep],
		 override val methods : Map[MethodId, MethodRep]
	) extends ClassRep {
		override val typeParameters : Map[TypeVarId, Sort] = Map()

		override def getField(fieldId : FieldId) : Option[FieldRep] =
			fields.get(fieldId)

		override def getMethod(methodId : MethodId) : Option[MethodRep] =
			methods.get(methodId)

		override def sortFactory : Seq[Sort] => Sort = args => {
			require(args.isEmpty)
			sort
		}
	}

	case class NativeClassRep(
		 override val sortFactory : Seq[Sort] => Sort,
		 override val typeParameters : Map[TypeVarId, Sort],
		 override val methods : Map[MethodId, MethodRep]
 	) extends ClassRep {
		override def getField(fieldId : FieldId) : Option[FieldRep] =
			None

		override def getMethod(methodId : MethodId) : Option[MethodRep] =
			methods.get(methodId)
	}

	case class FieldRep(funcDecl: FuncDecl[_])

	trait MethodRep {
		def funcDecl : FuncDecl[_]
	}
	case class QueryMethodRep(override val funcDecl: FuncDecl[_]) extends MethodRep
	case class UpdateMethodRep(override val funcDecl: FuncDecl[_]) extends MethodRep


	case class InvariantRep(funcDecl : FuncDecl[BoolSort])
}
