package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.ClassDef.{FieldDef, MethodDef}
import de.tuda.stg.consys.invariants.lang.ast.{Statement, Type}


case class ClassDef(
	name : ClassId,
	fields : Seq[FieldDef],
	methods : Seq[MethodDef]
) {

	def getMethod(methodId : MethodId) : Option[MethodDef] =
		methods.find(mDef => mDef.name == methodId)

	def getField(fieldId : FieldId) : Option[FieldDef] =
		fields.find(fDef => fDef.name == fieldId)


}

object ClassDef {
	case class VarDef(typ : Type, name : VarId)
	case class FieldDef(typ : Type, name : FieldId)
	case class MethodDef(typ : Type, name : MethodId, parameters : Seq[VarDef], body : Statement)

}
