package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, FuncDecl, Sort}
import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassId, FieldId, MethodId}
import de.tuda.consys.invariants.solver.next.translate.RepTable.{FieldRep, MethodRep, ParametrizedClassRep, ParametrizedNativeClassRep, ParametrizedObjectClassRep}
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.CachedMap

class RepTable(private val table : Map[ClassId, ParametrizedClassRep[_]]) {

	def getField(classId : ClassId, typeArguments : Seq[Sort], fieldId : FieldId) : Option[FieldRep] = {
		table.get(classId) match {
			case None => None
			case Some(classRep) =>
				classRep match {
					case objClass : ParametrizedObjectClassRep =>
						objClass.instances(typeArguments).fields.get(fieldId) match {
							case None => None
							case Some(field) => Some(field)
						}
					case natClass : ParametrizedNativeClassRep =>
						None
				}
		}
	}

	def getMethod(classId : ClassId, typeArguments : Seq[Sort], methodId : MethodId) : Option[MethodRep] = {
		table.get(classId) match {
			case None => None
			case Some(classRep) =>
				classRep match {
					case objClass : ParametrizedObjectClassRep =>
						objClass.instances(typeArguments).methods.get(methodId) match {
							case None => None
							case Some(field) => Some(field)
						}
					case natClass : ParametrizedNativeClassRep =>
						natClass.instances(typeArguments).methods.get(methodId) match {
							case None => None
							case Some(field) => Some(field)
						}
				}
		}
	}
}

object RepTable {
	sealed trait ParametrizedClassRep[Inst <: InstantiatedClassRep] {
		def instances : Seq[Sort] => Inst
	}

	sealed trait InstantiatedClassRep {
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

	class ParametrizedNativeClassRep(
		override val instances : CachedMap[Seq[Sort], InstantiatedNativeClassRep],
	) extends ParametrizedClassRep[InstantiatedNativeClassRep] {

	}

	class InstantiatedNativeClassRep(
		override val sort : Sort,
		val methods : Map[MethodId, MethodRep]
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