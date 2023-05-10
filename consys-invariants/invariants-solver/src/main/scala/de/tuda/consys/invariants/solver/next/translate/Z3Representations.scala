package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, FuncDecl, Sort, TupleSort}
import de.tuda.consys.invariants.solver.next.ir.IR.{ClassId, FieldId, MethodId, Type, TypeVarId}

import scala.collection.mutable


object Z3Representations {

	type RepTable = Map[ClassId, ParametrizedClassRep[_]]

	class CachedMap[A, B](f : A => B, entries : Map[A, B] = Map.empty) extends (A => B) {
		private val cache : mutable.Map[A, B] = mutable.Map.empty
		cache.addAll(entries)

		override def apply(v1 : A) : B =
			cache.getOrElseUpdate(v1, f(v1))
	}



	trait ParametrizedClassRep[Inst <: InstantiatedClassRep] {
		def instances : CachedMap[Seq[Sort], Inst]
	}

	trait InstantiatedClassRep {
		def sort : Sort

		def getField(fieldId : FieldId) : Option[FieldRep]
		def getMethod(methodId : MethodId) : Option[MethodRep]
	}

	class ParametrizedObjectClassRep(
		override val instances : CachedMap[Seq[Sort], InstantiatedObjectClassRep],
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

	class InstantiatedNativeClassRep(
		override val sort : Sort,
		methods : Map[MethodId, MethodRep]
 	) extends InstantiatedClassRep {
		override def getField(fieldId : FieldId) : Option[FieldRep] =
			None
		override def getMethod(methodId : MethodId) : Option[MethodRep] =
			methods.get(methodId)
	}

	case class FieldRep(sort : Sort, funcDecl: FuncDecl[_])

	trait MethodRep {
		def funcDecl : FuncDecl[_]
	}
	case class QueryMethodRep(override val funcDecl: FuncDecl[_]) extends MethodRep
	case class UpdateMethodRep(override val funcDecl: FuncDecl[_]) extends MethodRep


	case class InvariantRep(funcDecl : FuncDecl[BoolSort])
}
