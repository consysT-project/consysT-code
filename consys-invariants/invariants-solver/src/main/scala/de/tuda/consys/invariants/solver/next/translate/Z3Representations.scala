package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, FuncDecl, Sort, TupleSort}
import de.tuda.consys.invariants.solver.next.ir.IR.{ClassId, FieldId, MethodId, Type, TypeVarId}

import scala.collection.mutable


object Z3Representations {

	type RepTable = Map[ClassId, ParametrizedClassRep[_]]

	class CachedMap[A, B](f : A => B) extends (A => B) {
		private val cache : mutable.Map[A, B] = mutable.Map.empty

		override def apply(v1 : A) : B =
			cache.getOrElseUpdate(v1, f(v1))
	}



	trait ParametrizedClassRep[Inst <: InstantiatedClassRep] {
		def instances : CachedMap[Seq[Sort], Inst]
		def typeParameters : Seq[TypeVarId]
	}

	trait InstantiatedClassRep {
		def sort : Sort

		def getField(fieldId : FieldId) : Option[FieldRep]
		def getMethod(methodId : MethodId) : Option[MethodRep]
	}

	class ParametrizedObjectClassRep(
		override val instances : CachedMap[Seq[Sort], InstantiatedObjectClassRep],
		override val typeParameters : Seq[TypeVarId]
	) extends ParametrizedClassRep[InstantiatedObjectClassRep] {

	}

	class InstantiatedObjectClassRep(
		override val sort : Sort,
		val fields : Map[FieldId, FieldRep],
		val methods : Map[MethodId, MethodRep]
	) extends InstantiatedClassRep {
		override def getField(fieldId : FieldId) : Option[FieldRep] =
			fields.get(fieldId)

		override def getMethod(methodId : MethodId) : Option[MethodRep] =
			methods.get(methodId)
	}

//	case class ObjectClassRep(
//		 sort : CachedFun[Seq[Sort], TupleSort],
//		 fields : Map[FieldId, FieldRep],
//		 override val methods : Map[MethodId, MethodRep]
//	) extends ClassRep {
//		override val typeParameters : Map[TypeVarId, Sort] = Map()
//
//		override def getField(fieldId : FieldId) : Option[FieldRep] =
//			fields.get(fieldId)
//
//		override def getMethod(methodId : MethodId) : Option[MethodRep] =
//			methods.get(methodId)
//
//		override def sortFactory : Seq[Sort] => Sort = args => {
//			require(args.isEmpty)
//			sort
//		}
//	}

	class InstantiatedNativeClassRep(
		override val sort : Sort,
		methods : Map[MethodId, MethodRep]
 	) extends InstantiatedClassRep {
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
